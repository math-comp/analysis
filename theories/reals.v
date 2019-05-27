(* -------------------------------------------------------------------- *)
(* Copyright (c) - 2015--2016 - IMDEA Software Institute                *)
(* Copyright (c) - 2015--2018 - Inria                                   *)
(* Copyright (c) - 2016--2018 - Polytechnique                           *)

(* -------------------------------------------------------------------- *)
(* A very classical axiomatization of real numbers: a discrete real     *)
(* archimedean field with a least upper bound operator.                 *)
(* -------------------------------------------------------------------- *)

From mathcomp Require Import all_ssreflect all_algebra.
(* ------- *) Require Import boolp classical_preds classical_sets.

(* Require Import Setoid. *)

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import GRing.Theory Num.Theory.

(* -------------------------------------------------------------------- *)
Delimit Scope real_scope with real.

Local Open Scope real_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope prop_scope.
(* -------------------------------------------------------------------- *)
Section ArchiBound.

Variable (R : archiFieldType).

  (* Real set non-emptyness. *)
Definition nonempty (E : set (Num.ArchimedeanField.sort R)) :=
  exists x : R, x \in E.

(* Real upper bound and lower bound sets. *)
Definition ub (E : set R) : set R :=
  [set z | forall y, (y \in E) -> (y <= z)].
Definition lb (E : set R) : set R :=
  [set z | forall y, (y \in E) -> (z <= y)].

(* Real down set (i.e., generated order ideal) *)
(* i.e. down E := { x | exists y, y \in E /\ x <= y} *)
Definition down (E : set R) : set R :=
  [set x | exists2 y, (y \in E) & (x <= y)].

(* Real set supremum and infimum existence condition. *)
Definition has_ub  (E : set R) := nonempty (ub E).
Definition has_sup (E : set R) := nonempty E /\ has_ub E.
Definition has_lb  (E : set R) := nonempty (lb E).
Definition has_inf (E : set R) := nonempty E /\ has_lb E.

End ArchiBound.

(* -------------------------------------------------------------------- *)
Module Real.
Section Mixin.

Variable (R : archiFieldType).

Record mixin_of : Type := Mixin {
  sup : set (Num.ArchimedeanField.sort R) -> Num.ArchimedeanField.sort R;
   _  :
    forall E : set (Num.ArchimedeanField.sort R),
      has_sup E -> sup E \in ub E;
   _  :
    forall (E : set (Num.ArchimedeanField.sort R)) (eps : R),
      has_sup E -> 0 < eps -> exists2 e : R, E e & (sup E - eps) < e;
   _  :
    forall E : set (Num.ArchimedeanField.sort R),
      ~ has_sup E -> sup E = 0
}.

End Mixin.

Definition EtaMixin R sup sup_upper_bound sup_adherent :=
  let _ := @Mixin R sup sup_upper_bound sup_adherent in
  @Mixin (Num.ArchimedeanField.Pack (Num.ArchimedeanField.class R))
         sup sup_upper_bound sup_adherent.
Section ClassDef.

Record class_of (R : Type) : Type := Class {
  base : Num.ArchimedeanField.class_of R;
  mixin_rcf : Num.real_closed_axiom (Num.NumDomain.Pack base);
  mixin : mixin_of (Num.ArchimedeanField.Pack base)
}.

Local Coercion base : class_of >-> Num.ArchimedeanField.class_of.
Local Coercion base_rcf R (c : class_of R) : Num.RealClosedField.class_of R :=
  @Num.RealClosedField.Class _ c (@mixin_rcf _ c). 
  
Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition rcf_axiom {R} (cR : Num.RealClosedField.class_of R) :
   Num.real_closed_axiom (Num.NumDomain.Pack cR) :=
  match cR with Num.RealClosedField.Class _ ax => ax end.
Coercion rcf_axiom : Num.RealClosedField.class_of >-> Num.real_closed_axiom.

Definition pack b0 (m0 : mixin_of (@Num.ArchimedeanField.Pack T b0)) :=
  fun bT b & phant_id (Num.ArchimedeanField.class bT) b =>
  fun (bTr : rcfType) (br : Num.RealClosedField.class_of bTr) &
      phant_id (Num.RealClosedField.class bTr) br =>
  fun  cra & phant_id (@rcf_axiom bTr br) cra =>
  fun    m & phant_id m0 m => Pack (@Class T b cra m) T.

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition ringType := @GRing.Ring.Pack cT xclass.
Definition comRingType := @GRing.ComRing.Pack cT xclass.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT xclass.
Definition idomainType := @GRing.IntegralDomain.Pack cT xclass.
Definition numDomainType := @Num.NumDomain.Pack cT xclass.
Definition fieldType := @GRing.Field.Pack cT xclass.
Definition join_numDomainType := @Num.NumDomain.Pack fieldType xclass.
Definition realDomainType := @Num.RealDomain.Pack cT xclass.
Definition numFieldType := @Num.NumField.Pack cT xclass.
Definition join_realDomainType := @Num.RealDomain.Pack numFieldType xclass.
Definition realFieldType := @Num.RealField.Pack cT xclass.
Definition archimedeanFieldType := @Num.ArchimedeanField.Pack cT xclass.
Definition rcfType := @Num.RealClosedField.Pack cT xclass.
Definition join_rcfType := @Num.RealClosedField.Pack archimedeanFieldType xclass.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Num.ArchimedeanField.class_of.
Coercion base_rcf : class_of >-> Num.RealClosedField.class_of.
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
Coercion rcfType : type >-> Num.RealClosedField.type.
Canonical rcfType.
Canonical join_rcfType.

Notation realType := type.
Notation RealType T m := (@pack T _ m _ _ id _ _ id _ id _ id).
Notation RealMixin := EtaMixin.
Notation "[ 'realType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'realType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'realType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'realType'  'of'  T ]") : form_scope.

End Exports.
End Real.

Export Real.Exports.

(* -------------------------------------------------------------------- *)
Local Open Scope classical_set_scope.
(* todo: the same notation as in finset might be dangerous... *)

Definition sup {R : realType} := Real.sup (Real.class R).
Local Notation "-` E" := [set x | E (- x)]
                           (at level 35, right associativity) : fun_scope.

Definition inf {R : realType} (E : set (Num.ArchimedeanField.sort R)) :=
    - sup (-` E).

(* -------------------------------------------------------------------- *)
Section DefinitionUnfolding.
Context {R : archiFieldType}.

Implicit Types E : set (Num.ArchimedeanField.sort R).
Implicit Types x : R.

Lemma ubE E x : x \in ub E = forall y, y \in E -> y <= x.
Proof. by [].  Qed. 

Lemma lbE E x : x \in lb E = forall y, y \in E -> x <= y.
Proof. by []. Qed.

Lemma downE E x : x \in down E = exists2 y, y \in E & x <= y.
Proof. by []. Qed.

Lemma has_ubP {E} : has_ub E = nonempty (ub E).
Proof. by []. Qed.

Lemma has_lbP {E} : has_lb E = nonempty (lb E).
Proof. by []. Qed.

Lemma has_supP {E} : has_sup E = (nonempty E /\ nonempty (ub E)).
Proof. by []. Qed.

Lemma has_infP {E} : has_inf E = (nonempty E /\ nonempty (lb E)).
Proof. by []. Qed.

Lemma nz_has_supP E : nonempty E -> has_sup E = nonempty (ub E).
Proof.  move=> nz; rewrite has_supP propeqE; tauto. Qed.

Lemma nz_has_infP E : nonempty E -> has_inf E = nonempty (lb E).
Proof.  move=> nz; rewrite has_infP propeqE; tauto. Qed.

End DefinitionUnfolding.

(* -------------------------------------------------------------------- *)


Lemma sup_upper_bound {R : realType} (E : set (Num.ArchimedeanField.sort R)):
  has_sup E -> (forall x, x \in E -> x <= sup E).
Proof. by case: R E => /= R /= [] ? ? [].  Qed.

Lemma sup_adherent {R : realType} (E : set R) (eps : R) :
  has_sup E -> 0 < eps -> exists2 e : R, e \in E & (sup E - eps) < e.
Proof. by case: R E eps=> ? [? ? []]. Qed.

Lemma sup_out {R : realType} (E : set R) : ~ has_sup E -> sup E = 0.
Proof. by case: R E => ? [? ? []]. Qed.


Section IsInt.
Context {R : realType}.

Definition Rint := [qualify a x : R | asbool (exists z, x = z%:~R)].
Fact Rint_key : pred_key Rint. Proof. by []. Qed.
Canonical Rint_keyed := KeyedQualifier Rint_key.

Lemma Rint_def x : (x \is a Rint) = (asbool (exists z, x = z%:~R)).
Proof. by []. Qed.

Lemma RintP x : reflect (exists z, x = z%:~R) (x \in Rint).
Proof. by rewrite Rint_def; exact: asboolP. Qed.

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


(* This is a unique choice. *)
Definition Rtoint (x : R) : int :=
  if insub x : {? x | x \is a Rint} is Some Px then
   sval (constructive_indefinite_description (RintP _ (projT2 Px)))
  else 0.

Lemma RtointK (x : R): x \is a Rint -> (Rtoint x)%:~R = x.
Proof.
move=> Ix; rewrite /Rtoint insubT /=.
by set i := constructive_indefinite_description _; case: i => i hi /=.
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

Definition floor_set x := [ppred y | (y \is a Rint) && (y <= x)].

Definition floor x : R := sup (floor_set x).

Definition ifloor x : int := Rtoint (floor x).

Definition range1 (x : R) := [ppred y | x <= y < x + 1].

End RealDerivedOps.

(*-------------------------------------------------------------------- *)
Section RealLemmas.

Variables (R : realType).

Implicit Types E : set R.
Implicit Types x : R.

Lemma sup_ub {E} : has_ub E -> sup E \in ub E.
Proof.
move=> Ehas_ub /=; rewrite ubE => y Ey. (* boo: y \in (fun x : R => E x) *)
by apply/sup_upper_bound=> //; rewrite has_supP; split; first by exists y.
Qed.

Lemma sup_total {E} x : has_sup E -> (x \in down E) \/ (sup E <= x).
Proof.
move=> has_supE; case: (lerP (sup E) x)=> hx; [by right | left]. (* we miss comp. *)
have  /(sup_adherent has_supE) : 0 < sup E - x by rewrite subr_gt0.
case=> e Ee hlte; rewrite downE; exists e => //; move: hlte.
by rewrite opprB addrCA subrr addr0 => /ltrW.
Qed.

Lemma sup_le_ub {E} x : nonempty E -> x \in ub E -> sup E <= x.
Proof.
set y := sup E; pose z := (x + y) / 2%:R; rewrite ubE=> hasE ub_x.
have Dz : 2%:R * z = x + y by rewrite mulrCA divff ?mulr1 // pnatr_eq0.
have hyz : y <= z -> y + y <= 2%:R * z by rewrite -mulr2n mulr_natl ler_pmuln2r.
have hzx : z <= x -> 2%:R * z <= x + x by rewrite -mulr2n mulr_natl ler_pmuln2r.
have : z \in down E \/ y <= z by apply: sup_total; split; last by exists x; rewrite ubE.
case=> // [[t Et lezt] | /hyz]; last by rewrite Dz ler_add2r.
suff /hzx : z <= x by rewrite Dz ler_add2l.
apply: ler_trans lezt _; exact: ub_x.
Qed.

Lemma nonemptyPn {E} :
  (~ nonempty E) = (forall x, x \notin E).
Proof. by rewrite /nonempty not_exists. Qed.


(* still some fiddling because one cannot rewrite under binders *)
(* Should this be stated as an equality or an equivalence? *)
Lemma has_ubPn {E} :
  (~ has_ub E) <-> (forall x, exists2 y, y \in E & x < y).
Proof. 
rewrite /has_ub nonemptyPn; apply: forall_congr=> x; rewrite ubE not_forall. 
split; case => y; first by rewrite not_imply notb -ltrNge; case=> *; exists y.
by move=> *; exists y; rewrite not_imply notb -ltrNge.
Qed.

(* same remark, same problem, same proof as has_ubPn*)
Lemma has_supPn {E} : nonempty E ->
  (~ has_sup E) <-> (forall x, exists2 y, y \in E & x < y).
Proof.
move=> nzE. rewrite nz_has_supP // nonemptyPn. apply: forall_congr=> x.
rewrite ubE not_forall.
split; case => y; first by rewrite not_imply notb -ltrNge; case=> *; exists y.
by move=> *; exists y; rewrite not_imply notb -ltrNge.
Qed.

End RealLemmas.

(* -------------------------------------------------------------------- *)
Section InfTheory.

Variables (R : realType).

Implicit Types E : ppred R.
Implicit Types x : R.


Lemma setNK : involutive (fun E => -` E).
Proof. by move=> E; rewrite funeqE => ?; rewrite opprK. Qed.

Lemma memNNE E x : (x \in E) = (- x \in -` E).
Proof. by rewrite in_setE opprK. Qed.

Lemma memNE E x : (x \in -` E) = (- x \in E).
Proof. by rewrite -[X in X \in -` _]opprK -memNNE. Qed.

Lemma Nset1 x : -` [set x] = [set -x].
Proof. 
by apply: funext=> y; rewrite /set1 propeqE; split=> [<- | ->]; rewrite opprK. 
Qed.

Lemma lb_ubN E x : (x \in lb E) <-> - x \in ub (-` E).
Proof.
rewrite ubE lbE; split=> h t.
  by rewrite -{1}[t]opprK -memNNE => /h; rewrite ler_oppr.
by rewrite memNNE => /h; rewrite ler_opp2.
Qed.

Lemma ub_lbN E x : (x \in ub E) <-> - x \in lb (-` E).
Proof.
split; first by move=> ?; apply/lb_ubN; rewrite opprK setNK.
by move/lb_ubN; rewrite opprK setNK.
Qed.

Lemma nonemptyN E : nonempty (-` E) <-> nonempty E.
Proof. by split=> [[x ENx]|[x Ex]]; exists (- x) => //; rewrite -memNNE. Qed.

Lemma has_inf_supN E : has_inf E <-> has_sup (-` E).
Proof.
rewrite -propeqE has_infP has_supP (propext (nonemptyN _)); congr (_ /\ _).
rewrite propeqE; split; case=> x hx; exists (- x); first by apply/lb_ubN.
by apply/lb_ubN; rewrite opprK.
Qed.


Lemma inf_lower_bound E :
  has_inf E -> (forall x, x \in E -> inf E <= x).
Proof.
move=> /has_inf_supN /sup_upper_bound inflb x.
by rewrite memNNE => /inflb; rewrite ler_oppl.
Qed.

Lemma inf_adherent E (eps : R) :
  has_inf E -> 0 < eps -> exists2 e, e \in E & e < inf E + eps.
Proof.
move=> /has_inf_supN supNE /(sup_adherent supNE) [e NEx egtsup].
by exists (- e) => //; rewrite ltr_oppl -mulN1r mulrDr !mulN1r opprK.
Qed.

Lemma inf_out E : ~ has_inf E -> inf E = 0.
Proof.
move=> ninfE; rewrite -oppr0 -(@sup_out _ (-` E)) => // supNE; apply: ninfE.
exact/has_inf_supN.
Qed.

Lemma has_lb_ubN E : has_lb E <-> has_ub (-` E).
Proof.
rewrite has_lbP has_ubP; split=> [[x /lb_ubN] | [x /ub_lbN h]]; exists (-x) => //.
by rewrite setNK in h.
Qed.

Lemma inf_lb E : has_lb E -> inf E \in lb E.
Proof. by move/has_lb_ubN/sup_ub/ub_lbN; rewrite setNK. Qed.

Lemma lb_le_inf E x : nonempty E -> x \in lb E -> x <= inf E.
Proof.
by move=> /(nonemptyN E) En0 /lb_ubN /(sup_le_ub En0); rewrite ler_oppr.
Qed.

Lemma has_lbPn E :
  ~ has_lb E <-> (forall x, exists2 y, y \in E & y < x).
Proof.
split=> [/has_lb_ubN /has_ubPn NEnub x|Enlb /has_lb_ubN].
  by have [y ENy ltxy] := NEnub (- x); exists (- y) => //; rewrite ltr_oppl.
apply/has_ubPn => x; have [y Ey ltyx] := Enlb (- x); exists (- y).
  by rewrite in_setE opprK.
by rewrite ltr_oppr.
Qed.

Lemma has_infPn E : nonempty E ->
  ~ has_inf E <-> (forall x, exists2 y, y \in E & y < x).
Proof. 
move=> nzE. rewrite nz_has_infP // nonemptyPn. apply: forall_congr=> x.
rewrite lbE not_forall.
split; case => y; first by rewrite not_imply notb -ltrNge; case=> *; exists y.
by move=> *; exists y; rewrite not_imply notb -ltrNge.
Qed.

End InfTheory.

(* -------------------------------------------------------------------- *)
Section FloorTheory.
Variable R : realType.

Implicit Types x y : R.

Lemma has_sup_floor_set x: has_sup (floor_set x).
Proof.
split; [exists (- (Num.bound (-x))%:~R) | exists (Num.bound x)%:~R].
  rewrite in_setE /= rpredN rpred_int /= ler_oppl.
  case: (ger0P (-x)) => [/archi_boundP/ltrW//|].
  by move/ltrW/ler_trans; apply; rewrite ler0z.
rewrite ubE=> y /andP[_] /ler_trans; apply.
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
rewrite in_setE; have /andP[_ ->] /= := sup_in_floor_set x.
case: (lem (floor x + 1 \in floor_set x)). 
  by move/sup_upper_bound=> -/(_ (has_sup_floor_set x)); rewrite ger_addl ler10.
by rewrite in_setE => /negP; rewrite negb_and -ltrNge rpredD ?Rint1 // isint_floor.
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
Proof. by rewrite in_setE lerr /= ltr_addl ltr01. Qed.

Lemma range1zP (m : int) (x : R) :
  (floor x = m%:~R) <-> (x \in range1 m%:~R).
Proof.
split; first by move<-; apply/mem_rg1_floor.
move=> h; apply/eqP; rewrite floorE eqr_int; apply/eqP/(@range1z_inj x) => //.
rewrite -floorE; exact: mem_rg1_floor.
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

Implicit Types S : ppred R.

Lemma le_down S : {subset S <= down S}.
Proof. by move=> x xS; rewrite downE; exists x. Qed.

Lemma downK S : down (down S) =i down S.
Proof.
move=> x; rewrite !downE propeqE; split=> -[y yS le_xy]; last first.
  by exists y=> //; apply/le_down.
by case: yS => z zS le_yz; exists z => //; apply/(ler_trans le_xy).
Qed.

Lemma eq_ub S1 S2 : S2 =i S1 -> ub S2 =i ub S1.
Proof.
by move=> eq_12 x; rewrite propeqE; split=> h y yS; apply/h; 
rewrite (eq_12, =^~ eq_12).
Qed.

Lemma eq_lb S1 S2 : S2 =i S1 -> lb S2 =i lb S1.
Proof.
by move=> eq_12 x; rewrite propeqE; split=> h y yS; apply/h; 
rewrite (eq_12, =^~ eq_12).
Qed.

Lemma eq_has_sup S1 S2 : S2 =i S1 -> has_sup S2 -> has_sup S1.
Proof.
move=> eq_12 [[x xS2] [u uS2]]; split; first by exists x; rewrite -eq_12. 
by exists u; rewrite (@eq_ub S2).
Qed.

Lemma eq_has_inf S1 S2 : S2 =i S1 -> has_inf S2 -> has_inf S1.
Proof.
move=> eq_12 /has_inf_supN infS1; apply/has_inf_supN; apply: eq_has_sup infS1.
move=> x; rewrite in_setE /=; exact: eq_12.
Qed.

Lemma eq_has_supb S1 S2 :
   S2 =i S1 -> `[< has_sup S2 >] = `[< has_sup S1 >].
Proof. by move=> eq_12; apply/asboolP/asboolP; apply/eq_has_sup. Qed.

Lemma eq_has_supP S1 S2 : S2 =i S1 -> has_sup S2 = has_sup S1.
Proof. by move/eq_has_supb=> e; rewrite -[has_sup _]asboolE e asboolE. Qed.

Lemma eq_has_infb S1 S2 :
  S2 =i S1 -> `[< has_inf S2 >] = `[< has_inf S1 >].
Proof. by move=> eq_12; apply/asboolP/asboolP; apply/eq_has_inf. Qed.

Lemma eq_has_infP S1 S2 : S2 =i S1 -> has_inf S2 = has_inf S1.
Proof. by move/eq_has_infb=> e; rewrite -[has_inf _]asboolE e asboolE. Qed.

Lemma eq_sup S1 S2 : S2 =i S1 -> sup S2 = sup S1.
Proof.
wlog: S1 S2 / (sup S1 <= sup S2) => [wlog|le_S1S2] eq_12.
  by case: (lerP (sup S1) (sup S2)) => [|/ltrW] /wlog ->.
move: le_S1S2; rewrite ler_eqVlt => /orP[/eqP->//|lt_S1S2].
case: (lem (has_sup S2)) => h2; last by rewrite !sup_out // -(eq_has_supP eq_12). 
pose x : R := sup S2 - sup S1; have gt0_x: 0 < x by rewrite subr_gt0.
have [e eS2] := sup_adherent h2 gt0_x; rewrite subKr => lt_S1e.
have /(eq_has_sup eq_12) h1 := h2; have := eS2; rewrite eq_12.
by move/sup_upper_bound=> -/(_ h1); rewrite lerNgt lt_S1e.
Qed.


Lemma eq_inf S1 S2 : S2 =i S1 -> inf S2 = inf S1.
Proof.
move=> e; rewrite /inf; apply/congr1/eq_sup => x; rewrite !in_setE /=; exact: e.
Qed.


Lemma has_sup_down S : has_sup (down S) <-> has_sup S.
Proof.
split; case => [nzS nzubS].
  case: nzS=> x [y yS le_xy]; split; first by exists y.
  by case: nzubS=> u ubS; exists u => z zS; apply/ubS; exists z.
case: nzS=> x xS; split; first by exists x; apply/le_down.
by case: nzubS=> u ubS; exists u => y [] z zS /ler_trans; apply; apply/ubS.
Qed.

Lemma le_sup S1 S2 :
  {subset S1 <= down S2} -> nonempty S1 -> has_sup S2 -> sup S1 <= sup S2.
Proof.
move=> le_S12 nz_S1 hs_S2. 
have hs_S1: has_sup S1.
  split=> //; case: hs_S2=> _ [x ubx]; exists x => y /le_S12 [z zS2 le_yz].
  by apply/(ler_trans le_yz); apply: ubx.
rewrite lerNgt -subr_gt0; apply/negP => lt_sup.
case: (sup_adherent hs_S1 lt_sup)=> x /le_S12 xdS2.
rewrite subKr => lt_S2x; case: xdS2=> z zS2.
by move/(ltr_le_trans lt_S2x); rewrite ltrNge sup_upper_bound.
Qed.

Lemma sup_down S : sup (down S) = sup S.
Proof.
case: (lem (has_sup S)); last first.
  by move=> supNS; rewrite !sup_out // => /has_sup_down.
move=> supS; have supDS: has_sup (down S) by apply/has_sup_down.
apply/eqP; rewrite eqr_le !le_sup //; last by case: supS.
  by case: supS => -[x xS] _; exists x; apply/le_down.
move=> x xS; rewrite downK; exact: le_down.
Qed.

Lemma sup1 (c : R) : sup (set1 c) = c.
Proof.
have hs: has_sup (set1 c). 
  by split; exists c; rewrite ?set1P // ubE => y; rewrite set1P=>->. 
apply/eqP; rewrite eqr_le sup_upper_bound ?inE // andbT.
apply/sup_le_ub; first by exists c; rewrite in_setE. 
by rewrite ubE => y; rewrite in_setE => ->.
Qed.


Lemma inf1 (c : R) : inf (set1 c) = c.
Proof.
suff: -` (set1 c) =i set1 (- c) by rewrite /inf; move/eq_sup->; rewrite sup1 opprK.
by move=> x; rewrite Nset1. (* notation -` vanishes *)
Qed.

Lemma lt_sup_imfset {T : Type} (F : T -> R) l :
  has_sup [set y | exists x, y = F x] ->
  l < sup [set y | exists x, y = F x] ->
  exists2 x, l < F x & F x <= sup [set y | exists x, y = F x].
Proof.
set P := [set y | _]; move=> hs; rewrite -subr_gt0.
case/(sup_adherent hs)=> y; rewrite in_setE; case => x ->; rewrite subKr => lt_lFx. 
by exists x=> //; apply/sup_upper_bound => //; exists x. 
Qed.

Lemma lt_inf_imfset {T : Type} (F : T -> R) l :
  has_inf [set y | exists x, y = F x] -> inf [set y | exists x, y = F x] < l ->
  exists2 x, F x < l & inf [set y | exists x, y = F x] <= F x.
Proof.
set P := [set y | _]; move=> hs; rewrite -subr_gt0.
case/(inf_adherent hs)=> y; rewrite in_setE [l - _]addrC addNKr; case => x ->.
by move=> ltFxl; exists x=> //; apply/inf_lower_bound => //; exists x.
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

Lemma lee_trans : transitive (@lee R).
Proof. by move=> x y z; elift ler_trans : x y z. Qed.

Lemma lte_trans : transitive (@lte R).
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