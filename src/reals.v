(* -------------------------------------------------------------------- *)
(* A very classical axiomatization of real numbers: a discrete real     *)
(* archimedean field with a least upper bound operator.                 *)
(* -------------------------------------------------------------------- *)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import finset bigop ssralg ssrnum ssrint rat poly bigenough.
Require Import boolp ssrprop collections Setoid.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory BigEnough.

Local Ltac idone := solve [intuition] || ssreflect.done.

(* -------------------------------------------------------------------- *)
Delimit Scope real_scope with real.

Local Open Scope real_scope.
Local Open Scope ring_scope.

(* -------------------------------------------------------------------- *)
Module Real.
Section Mixin.

Variable (R : archiFieldType).

(* Real set non-emptyness. *)
Definition nonempty (E : {rset R}) :=
  exists x : R, x \mem E.

(* Real upper bound set. *)
Definition ub  (E : {rset R}) :=
  {{ z | forall y : R, E y -> y <= z }}.

(* Real down set (i.e., generated order ideal) *)
(* i.e. down E := { x | exists y, y \in E /\ x <= y} *)
Definition down  (E : {rset R}) :=
  {{ x | exists2 y : R, E y & x <= y }}.

(* Real set supremum existence condition. *)
Definition has_ub  (E : {rset R}) := nonempty (ub E).
Definition has_sup (E : {rset R}) := nonempty E /\ has_ub E.

Record mixin_of : Type := Mixin {
  sup : {rset R} -> R;
   _  :
    forall E : {rset Num.ArchimedeanField.sort R},
      has_sup E -> sup E \mem ub E;
   _  :
    forall (E : {rset Num.ArchimedeanField.sort R}) (eps : R),
      has_sup E -> 0 < eps -> exists2 e : R, E e & (sup E - eps) < e
}.

End Mixin.

Definition EtaMixin R sup sup_upper_bound sup_adherent :=
  let _ := @Mixin R sup sup_upper_bound sup_adherent in
  @Mixin (Num.ArchimedeanField.Pack (Num.ArchimedeanField.class R) R)
         sup sup_upper_bound sup_adherent.

Global Arguments ub      {R}%type _%rset_scope.
Global Arguments has_ub  {R}%type _%rset_scope.
Global Arguments has_sup {R}%type _%rset_scope.
Global Arguments down    {R}%type _%rset_scope.

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

Implicit Types E : {rset R}.
Implicit Types x : R.

Lemma nonemptyP E : nonempty E <-> exists x, E x.
Proof. by []. Qed.

Lemma ubP E x : x \mem ub E <-> (forall y, y \mem E -> y <= x).
Proof. by rewrite !in_rset. Qed.

Lemma downP E x : x \mem down E <-> exists2 y, y \mem E & x <= y.
Proof. by rewrite !in_rset. Qed.

Lemma has_ubP E : has_ub E <-> nonempty (ub E).
Proof. by []. Qed.

Lemma has_supP E : has_sup E <-> (nonempty E /\ nonempty (ub E)).
Proof. by []. Qed.
End BaseReflect.

(* -------------------------------------------------------------------- *)
Lemma sup_upper_bound {R : realType} (E : {rset R}) :
  has_sup E -> (forall x, x \mem E -> x <= sup E).
Proof. by move=> supE; apply/ubP; case: R E supE=> ? [? []]. Qed.

Lemma sup_adherent {R : realType} (E : {rset R}) (eps : R) :
  has_sup E -> 0 < eps -> exists2 e : R, E e & (sup E - eps) < e.
Proof. by case: R E eps=> ? [? []]. Qed.

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
Proof. by move=> Ix; rewrite /Rtoint insubT /= [RHS](eqP (xchoosebP Ix)). Qed.

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

Definition pickR_set P1 P2 (x1 x2 : R) :=
  {{ y | P1 /\ y = x1 \/ P2 /\ y = x2 }}.

Definition pickR P1 P2 x1 x2 := sup (pickR_set P1 P2 x1 x2).

Definition selectR P : R -> R -> R := pickR P (~ P).

Definition min x1 x2 := pickR (x1 <= x2) (x2 <= x1) x1 x2.

Definition max x1 x2 := pickR (x1 <= x2) (x2 <= x1) x2 x1.

Definition floor_set x := {{ y | (y \is a Rint) && (y <= x) }}.

Definition floor x : R := sup (floor_set x).

Definition ifloor x : int := Rtoint (floor x).

Definition range1 (x : R) := {{ y | x <= y < x + 1 }}.
End RealDerivedOps.

Notation "'select' { x1 'if' P1 , x2 'if' P2 }" := (pickR P1 P2 x1 x2)
   (at level 10, x1, x2, P1, P2 at level 100,
    format "'select'  { x1  'if'  P1 ,  x2  'if'  P2 }") : real_scope.

Notation "'select' { x1 'if' P , 'else' x2 }" := (selectR P x1 x2)
   (at level 10, x1, x2, P at level 100,
    format "'select'  { x1  'if'  P ,  'else'  x2 }") : real_scope.

Prenex Implicits min max.

(*-------------------------------------------------------------------- *)
Section RealLemmas.

Variables (R : realType).

Implicit Types E : {rset R}.
Implicit Types x : R.

Lemma sup_ub E : has_ub E -> sup E \mem ub E.
Proof.
move=> ubE; apply/ubP=> x x_in_E; apply/sup_upper_bound=> //.
by apply/has_supP; split; first by exists x.
Qed.

Lemma sup_total E x : has_sup E -> x \mem down E \/ sup E <= x.
Proof.
move=> has_supE; case: (lerP (sup E) x)=> hx; [idone|left].
have /(sup_adherent has_supE) : 0 < sup E - x by rewrite subr_gt0.
case=> e Ee hlte; apply/downP; exists e => //; move: hlte.
by rewrite opprB addrCA subrr addr0 => /ltrW.
Qed.

Lemma sup_le_ub E x : nonempty E -> x \mem ub E -> sup E <= x.
Proof.
move=> hasE /ubP leEx; set y := sup E; pose z := (x + y) / 2%:R.
have Dz: 2%:R * z = x + y.
  by rewrite mulrCA divff ?mulr1 // pnatr_eq0.
have ubE: has_sup E by split; last by exists x; apply/ubP.
have [/in_rset [t Et lezt] | leyz] := sup_total z ubE.
  rewrite -(ler_add2l x) -Dz -mulr2n -[X in _<=X]mulr_natl.
  rewrite ler_pmul2l ?ltr0Sn //; exact/(ler_trans lezt)/leEx.
rewrite -(ler_add2r y) -Dz -mulr2n -[X in X<=_]mulr_natl.
by rewrite ler_pmul2l ?ltr0Sn.
Qed.
End RealLemmas.

(* -------------------------------------------------------------------- *)
Section FloorTheory.
Variable R : realType.

Implicit Types x y : R.

Lemma has_sup_floor_set : forall x, has_sup (floor_set x).
Proof.
move=> x; split; [exists (- (Num.bound (-x))%:~R) | exists (Num.bound x)%:~R].
  apply/in_rset; rewrite rpredN rpred_int /= ler_oppl.
  case: (ger0P (-x)) => [/archi_boundP/ltrW//|].
  by move/ltrW/ler_trans; apply; rewrite ler0z.
apply/in_rset=> y /in_rset /andP[_] /ler_trans; apply.
case: (ger0P x)=> [/archi_boundP/ltrW|] //.
by move/ltrW/ler_trans; apply; rewrite ler0z.
Qed.

Lemma isint_floor : forall x, floor x \is a Rint.
Proof.
move=> x; suff: sup (floor_set x) \mem floor_set x.
  by case/in_rset/andP.
have /sup_adherent /(_ ltr01) [y Fy] := has_sup_floor_set x.
have /sup_upper_bound /(_ _ Fy) := has_sup_floor_set x.
rewrite ler_eqVlt=> /orP[/eqP<-//| lt_yFx].
rewrite ltr_subl_addr -ltr_subl_addl => lt1_FxBy.
pose e := sup (floor_set x) - y; have := has_sup_floor_set x.
move/sup_adherent=> -/(_ e) []; first by rewrite subr_gt0.
move=> z Fz; rewrite /e opprB addrCA subrr addr0 => lt_yz.
have /sup_upper_bound /(_ _ Fz) := has_sup_floor_set x.
rewrite -(ler_add2r (-y)) => /ler_lt_trans /(_ lt1_FxBy).
case/in_rset/andP: Fy Fz lt_yz=> /RintP[yi -> _]. 
case/in_rset/andP=> /RintP[zi -> _]; rewrite -rmorphB /= ltrz1 ltr_int.
rewrite ltr_neqAle => /andP[ne_yz le_yz].
rewrite -[_-_]gez0_abs ?subr_ge0 // ltz_nat ltnS leqn0.
by rewrite absz_eq0 subr_eq0 eq_sym (negbTE ne_yz).
Qed.

Lemma floorE x : floor x = (ifloor x)%:~R.
Proof. by rewrite /ifloor RtointK ?isint_floor. Qed.
End FloorTheory.
