(* -------------------------------------------------------------------- *)
(* Copyright (c) - 2015--2016 - IMDEA Software Institute                *)
(* Copyright (c) - 2015--2018 - Inria                                   *)
(* Copyright (c) - 2016--2018 - Polytechnique                           *)

(* -------------------------------------------------------------------- *)
(* A very classical axiomatization of real numbers: a discrete real     *)
(* archimedean field with a least upper bound operator.                 *)
(* -------------------------------------------------------------------- *)

From mathcomp Require Import all_ssreflect all_algebra.
(* ------- *) Require Import boolp classical_sets.

Require Import Setoid.

Declare Scope real_scope.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Unset SsrOldRewriteGoalsOrder.

Import Order.TTheory Order.Syntax GRing.Theory Num.Theory.

(* -------------------------------------------------------------------- *)
Delimit Scope real_scope with real.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section subr_image.
Variable R : numDomainType.
Implicit Types E : set R.
Implicit Types x : R.

Lemma setNK : involutive (fun E => -%R @` E).
Proof.
move=> F; rewrite predeqE => y; split => [|Fy].
  by case=> z -[u xu <-{z} <-{y}]; rewrite opprK.
by exists (- y); rewrite ?opprK //; exists y.
Qed.

Lemma memNE E x : E x = (-%R @` E) (- x).
Proof.
rewrite propeqE; split => [Ex|[y Ey]]; [by exists x|].
by move/eqP; rewrite eqr_opp => /eqP <-.
Qed.

Lemma lb_ubN E x : lbound E x <-> ubound (-%R @` E) (- x).
Proof.
split=> [/lbP xlbE|/ubP xlbE].
by apply/ubP=> y [z Ez <-{y}]; rewrite ler_oppr opprK; apply xlbE.
by apply/lbP => y Ey; rewrite -(opprK x) ler_oppl; apply xlbE; exists y.
Qed.

Lemma ub_lbN E x : ubound E x <-> lbound (-%R @` E) (- x).
Proof.
split=> [? | /lb_ubN].
by apply/lb_ubN; rewrite opprK setNK.
by rewrite opprK setNK.
Qed.

Lemma nonemptyN E : nonempty (-%R @` E) <-> nonempty E.
Proof.
split=> [[x ENx]|[x Ex]]; exists (- x); last by rewrite -memNE.
by rewrite memNE opprK.
Qed.

Lemma has_lb_ubN E : has_lbound E <-> has_ubound (-%R @` E).
Proof.
by split=> [[x /lb_ubN] | [x /ub_lbN]]; [|rewrite setNK]; exists (- x).
Qed.

Lemma has_lbound0 : has_lbound (@set0 R). Proof. by exists 0. Qed.

Lemma has_ubound0 : has_ubound (@set0 R). Proof. by exists 0. Qed.

End subr_image.

Section has_bound_lemmas.
Variable R : realDomainType.
Implicit Types E : set R.
Implicit Types x : R.

Lemma has_ubPn {E} : ~ has_ubound E <-> (forall x, exists2 y, E y & x < y).
Proof.
split; last first.
  move=> h [x] /ubP hle; case/(_ x): h => y /hle.
  by rewrite leNgt => /negbTE ->.
move/forallNP => h x; have {h} := h x.
move=> /ubP /existsNP => -[y /not_implyP[Ey /negP]].
by rewrite -ltNge => ltx; exists y.
Qed.

Lemma has_lbPn E : ~ has_lbound E <-> (forall x, exists2 y, E y & y < x).
Proof.
split=> [/has_lb_ubN /has_ubPn NEnub x|Enlb /has_lb_ubN].
  have [y ENy ltxy] := NEnub (- x); exists (- y); rewrite 1?ltr_oppl //.
  by case: ENy => z Ez <-; rewrite opprK.
apply/has_ubPn => x; have [y Ey ltyx] := Enlb (- x).
exists (- y); last by rewrite ltr_oppr.
by exists y => //; rewrite opprK.
Qed.

End has_bound_lemmas.

(* -------------------------------------------------------------------- *)
Module Real.
Section Mixin.

Variable (R : archiFieldType).

Record mixin_of : Type := Mixin {
  sup : set R -> R;
   _  :
    forall E : set (Num.ArchimedeanField.sort R),
      has_sup E -> ubound E (sup E);
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
  (* TODO: ajouter une structure de pseudoMetricNormedDomain *)
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
Definition porderType := @Order.POrder.Pack ring_display cT xclass.
Definition latticeType := @Order.Lattice.Pack ring_display cT xclass.
Definition distrLatticeType := @Order.DistrLattice.Pack ring_display cT xclass.
Definition orderType := @Order.Total.Pack ring_display cT xclass.
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition ringType := @GRing.Ring.Pack cT xclass.
Definition comRingType := @GRing.ComRing.Pack cT xclass.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT xclass.
Definition idomainType := @GRing.IntegralDomain.Pack cT xclass.
Definition numDomainType := @Num.NumDomain.Pack cT xclass.
Definition normedZmodType := NormedZmodType numDomainType cT xclass.
Definition fieldType := @GRing.Field.Pack cT xclass.
Definition realDomainType := @Num.RealDomain.Pack cT xclass.
Definition numFieldType := @Num.NumField.Pack cT xclass.
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
Coercion porderType : type >-> Order.POrder.type.
Canonical porderType.
Coercion latticeType : type >-> Order.Lattice.type.
Canonical latticeType.
Coercion distrLatticeType : type >-> Order.DistrLattice.type.
Canonical distrLatticeType.
Coercion orderType : type >-> Order.Total.type.
Canonical orderType.
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
Coercion normedZmodType : type >-> Num.NormedZmodule.type.
Canonical normedZmodType.
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
Definition sup {R : realType} := Real.sup (Real.class R).
(*Local Notation "-` E" := [pred x | - x \in E]
  (at level 35, right associativity) : fun_scope.*)
Definition inf {R : realType} (E : set R) := - sup (-%R @` E).

(* -------------------------------------------------------------------- *)

Lemma sup_upper_bound {R : realType} (E : set R):
  has_sup E -> ubound E (sup E).
Proof. by move=> supE; case: R E supE=> ? [? ? []]. Qed.

Lemma sup_adherent {R : realType} (E : set R) (eps : R) :
  has_sup E -> 0 < eps -> exists2 e : R, E e & (sup E - eps) < e.
Proof. by case: R E eps=> ? [? ? []]. Qed.

Lemma sup_out {R : realType} (E : set R) : ~ has_sup E -> sup E = 0.
Proof. by case: R E => ? [? ? []]. Qed.

(* -------------------------------------------------------------------- *)
Section IsInt.
Context {R : realFieldType}.

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

Hint Resolve Rint0 Rint1 RintC : core.

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

Lemma RtointN x : x \is a Rint -> Rtoint (- x) = - Rtoint x.
Proof.
move=> Ir; apply/eqP.
by rewrite -(@eqr_int R) RtointK // ?rpredN // mulrNz RtointK.
Qed.

End ToInt.

(* -------------------------------------------------------------------- *)
Section RealDerivedOps.
Variable R : realType.

Implicit Types x y : R.
Definition floor_set x := [set y : R | (y \is a Rint) && (y <= x)].

Definition Rfloor x : R := sup (floor_set x).

Definition floor x : int := Rtoint (Rfloor x).

Definition range1 (x : R) := [set y | x <= y < x + 1].

Definition Rceil x := - Rfloor (- x).

Definition ceil x := - floor (- x).

End RealDerivedOps.

(*-------------------------------------------------------------------- *)
Section RealLemmas.

Variables (R : realType).

Implicit Types E : set R.
Implicit Types x : R.

Lemma sup0 : sup (@set0 R) = 0.
Proof. by rewrite sup_out //; exact: has_sup0. Qed.

Lemma sup_ub {E} : has_ubound E -> (ubound E) (sup E).
Proof.
move=> ubE; apply/ubP=> x x_in_E; move: (x) (x_in_E).
by apply/ubP/sup_upper_bound=> //; split; first by exists x.
Qed.

Lemma sup_total {E} x : has_sup E -> (down E) x \/ sup E <= x.
Proof.
move=> has_supE; rewrite orC.
case: (lerP (sup E) x)=> hx /=; [by left|right].
have /(sup_adherent has_supE) : 0 < sup E - x by rewrite subr_gt0.
case=> e Ee hlte; apply/downP; exists e => //; move: hlte.
by rewrite opprB addrCA subrr addr0 => /ltW.
Qed.

Lemma sup_le_ub {E} x : E !=set0 -> (ubound E) x -> sup E <= x.
Proof.
move=> hasE leEx; set y := sup E; pose z := (x + y) / 2%:R.
have Dz: 2%:R * z = x + y.
  by rewrite mulrCA divff ?mulr1 // pnatr_eq0.
have ubE : has_sup E by split => //; exists x.
have [/downP [t Et lezt] | leyz] := sup_total z ubE.
  rewrite -(ler_add2l x) -Dz -mulr2n -[X in _<=X]mulr_natl.
  rewrite ler_pmul2l ?ltr0Sn //; apply/(le_trans lezt).
  by move/ubP : leEx; exact.
rewrite -(ler_add2r y) -Dz -mulr2n -[X in X<=_]mulr_natl.
by rewrite ler_pmul2l ?ltr0Sn.
Qed.

Lemma has_supPn {E} : E !=set0 ->
  ~ has_sup E <-> (forall x, exists2 y, E y & x < y).
Proof.
move=> nzE; split=> [/asboolPn|/has_ubPn h [_]] //.
by rewrite asbool_and (asboolT nzE) /= => /asboolP/has_ubPn.
Qed.

Lemma sup_setU (A B : set R) : has_sup B ->
  (forall a b, A a -> B b -> a <= b) -> sup (A `|` B) = sup B.
Proof.
move=> [B0 [l Bl]] AB; apply/eqP; rewrite eq_le; apply/andP; split.
- apply sup_le_ub => [|x [Ax|]]; first by apply: subset_nonempty B0 => ?; right.
  by case: B0 => b Bb; rewrite (le_trans (AB _ _ Ax Bb)) // sup_ub //; exists l.
- by move=> Bx; rewrite sup_ub //; exists l.
- apply sup_le_ub => // b Bb; apply sup_ub; last by right.
  by exists l => x [Ax|Bx]; [rewrite (le_trans (AB _ _ Ax Bb)) // Bl|exact: Bl].
Qed.

End RealLemmas.

(* -------------------------------------------------------------------- *)
Section InfTheory.

Variables (R : realType).

Implicit Types E : set R.
Implicit Types x : R.

Lemma has_inf_supN E : has_inf E <-> has_sup (-%R @` E).
Proof.
split=> [ [En0 [x /lb_ubN xlbe]] | [NEn0 [x /ub_lbN xubE]] ].
by split; [apply/nonemptyN|exists (- x)].
by split; [apply/nonemptyN|rewrite -[E]setNK; exists (- x)].
Qed.

Lemma inf_lower_bound E : has_inf E -> lbound E (inf E).
Proof.
move=> /has_inf_supN /sup_upper_bound /ubP inflb; apply/lbP => x.
by rewrite memNE => /inflb; rewrite ler_oppl.
Qed.

Lemma inf_adherent E (eps : R) :
  has_inf E -> 0 < eps -> exists2 e, E e & e < inf E + eps.
Proof.
move=> /has_inf_supN supNE /(sup_adherent supNE) [e NEx egtsup].
exists (- e); first by case: NEx => x Ex <-{}; rewrite opprK.
by rewrite ltr_oppl -mulN1r mulrDr !mulN1r opprK.
Qed.

Lemma inf_out E : ~ has_inf E -> inf E = 0.
Proof.
move=> ninfE; rewrite -oppr0 -(@sup_out _ (-%R @` E)) => // supNE; apply: ninfE.
exact/has_inf_supN.
Qed.

Lemma inf0 : inf (@set0 R) = 0.
Proof. by rewrite inf_out //; exact: has_inf0. Qed.

Lemma inf_lb E : has_lbound E -> (lbound E) (inf E).
Proof. by move/has_lb_ubN/sup_ub/ub_lbN; rewrite setNK. Qed.

Lemma lb_le_inf E x : nonempty E -> (lbound E) x -> x <= inf E.
Proof.
by move=> /(nonemptyN E) En0 /lb_ubN /(sup_le_ub En0); rewrite ler_oppr.
Qed.

Lemma has_infPn E : nonempty E ->
  ~ has_inf E <-> (forall x, exists2 y, E y & y < x).
Proof.
move=> nzE; split=> [/asboolPn|/has_lbPn h [_] //].
by rewrite asbool_and (asboolT nzE) /= => /asboolP/has_lbPn.
Qed.

Lemma inf_setU (A B : set R) : has_inf A ->
  (forall a b, A a -> B b -> a <= b) -> inf (A `|` B) = inf A.
Proof.
move=> hiA AB; congr (- _).
rewrite image_setU setUC sup_setU //; first exact/has_inf_supN.
by move=> _ _ [] b Bb <-{} [] a Aa <-{}; rewrite ler_oppl opprK; apply AB.
Qed.

End InfTheory.

(* -------------------------------------------------------------------- *)
Section FloorTheory.
Variable R : realType.

Implicit Types x y : R.

Lemma has_sup_floor_set x : has_sup (floor_set x).
Proof.
split; [exists (- (Num.bound (-x))%:~R) | exists (Num.bound x)%:~R].
  rewrite /floor_set/mkset rpredN rpred_int /= ler_oppl.
  case: (ger0P (-x)) => [/archi_boundP/ltW//|].
  by move/ltW/le_trans; apply; rewrite ler0z.
apply/ubP=> y /andP[_] /le_trans; apply.
case: (ger0P x)=> [/archi_boundP/ltW|] //.
by move/ltW/le_trans; apply; rewrite ler0z.
Qed.

Lemma sup_in_floor_set x : (floor_set x) (sup (floor_set x)).
Proof.
have /sup_adherent /(_ ltr01) [y Fy] := has_sup_floor_set x.
have /sup_upper_bound /ubP /(_ _ Fy) := has_sup_floor_set x.
rewrite le_eqVlt=> /orP[/eqP<-//| lt_yFx].
rewrite ltr_subl_addr -ltr_subl_addl => lt1_FxBy.
pose e := sup (floor_set x) - y; have := has_sup_floor_set x.
move/sup_adherent=> -/(_ e) []; first by rewrite subr_gt0.
move=> z Fz; rewrite /e opprB addrCA subrr addr0 => lt_yz.
have /sup_upper_bound /ubP /(_ _ Fz) := has_sup_floor_set x.
rewrite -(ler_add2r (-y)) => /le_lt_trans /(_ lt1_FxBy).
case/andP: Fy Fz lt_yz=> /RintP[yi -> _].
case/andP=> /RintP[zi -> _]; rewrite -rmorphB /= ltrz1 ltr_int.
rewrite lt_neqAle => /andP[ne_yz le_yz].
rewrite -[_-_]gez0_abs ?subr_ge0 // ltz_nat ltnS leqn0.
by rewrite absz_eq0 subr_eq0 eq_sym (negbTE ne_yz).
Qed.

Lemma isint_Rfloor x : Rfloor x \is a Rint.
Proof. by case/andP: (sup_in_floor_set x). Qed.

Lemma RfloorE x : Rfloor x = (floor x)%:~R.
Proof. by rewrite /floor RtointK ?isint_Rfloor. Qed.

Lemma mem_rg1_Rfloor x : (range1 (Rfloor x)) x.
Proof.
rewrite /range1/mkset.
have /andP[_ ->] /= := sup_in_floor_set x.
have [|] := pselect ((floor_set x) (Rfloor x + 1)); last first.
  rewrite /floor_set => /negP.
  by rewrite negb_and -ltNge rpredD // ?(Rint1, isint_Rfloor).
move/ubP : (sup_upper_bound (has_sup_floor_set x)) => h/h.
by rewrite ger_addl ler10.
Qed.

Lemma ge_Rfloor x : Rfloor x <= x.
Proof. by case/andP: (mem_rg1_Rfloor x). Qed.

Lemma ler_floor x : (floor x)%:~R <= x.
Proof. by rewrite -RfloorE; exact: ge_Rfloor. Qed.

Lemma lt_succ_Rfloor x : x < Rfloor x + 1.
Proof. by case/andP: (mem_rg1_Rfloor x). Qed.

Lemma range1z_inj x (m1 m2 : int) :
  (range1 m1%:~R) x -> (range1 m2%:~R) x -> m1 = m2.
Proof.
move=> /andP[m1x x_m1] /andP[m2x x_m2].
wlog suffices: m1 m2 m1x {x_m1 m2x} x_m2 / (m1 <= m2).
  by move=> ih; apply/eqP; rewrite eq_le !ih.
rewrite -(ler_add2r 1) lez_addr1 -(@ltr_int R) intrD.
exact/(le_lt_trans m1x).
Qed.

Lemma range1rr x : (range1 x) x.
Proof. by rewrite /range1/mkset lexx /= ltr_addl ltr01. Qed.

Lemma range1zP (m : int) x : Rfloor x = m%:~R <-> (range1 m%:~R) x.
Proof.
split=> [<-|h]; first exact/mem_rg1_Rfloor.
apply/eqP; rewrite RfloorE eqr_int; apply/eqP/(@range1z_inj x) => //.
by rewrite /range1/mkset -RfloorE mem_rg1_Rfloor.
Qed.

Lemma Rfloor_natz (n : int) : Rfloor n%:~R = n%:~R :> R.
Proof. by apply/range1zP/range1rr. Qed.

Lemma Rfloor0 : Rfloor 0 = 0 :> R.
Proof. by rewrite -{1}(mulr0z 1) Rfloor_natz. Qed.

Lemma Rfloor1 : Rfloor 1 = 1 :> R.
Proof. by rewrite -{1}(mulr1z 1) Rfloor_natz. Qed.

Lemma Rfloor_le : {homo (@Rfloor R) : x y / x <= y}.
Proof.
move=> x y le_xy; case: lerP=> //=; rewrite -Rint_ler_addr1 ?isint_Rfloor //.
move/(lt_le_trans (lt_succ_Rfloor y))/lt_le_trans/(_ (ge_Rfloor x)).
by rewrite ltNge le_xy.
Qed.

Lemma Rfloor_ge_int x (n : int) : (n%:~R <= x)= (n%:~R <= Rfloor x).
Proof.
apply/idP/idP; last by move/le_trans => /(_ _ (ge_Rfloor x)).
by move/Rfloor_le; apply le_trans; rewrite Rfloor_natz.
Qed.

Lemma Rfloor_le0 x : x <= 0 -> Rfloor x <= 0.
Proof. by move=> ?; rewrite -Rfloor0 Rfloor_le. Qed.

Lemma Rfloor_lt0 x : x < 0 -> Rfloor x < 0.
Proof. by move=> x0; rewrite (le_lt_trans _ x0) // ge_Rfloor. Qed.

Lemma floor_ge0 x : (0 <= floor x) = (0 <= x).
Proof. by rewrite -(@ler_int R) -RfloorE -Rfloor_ge_int. Qed.

Lemma floor_le0 x : x <= 0 -> floor x <= 0.
Proof. by move=> ?; rewrite -(@ler_int R) -RfloorE Rfloor_le0. Qed.

Lemma floor_lt0 x : x < 0 -> floor x < 0.
Proof.
by move=> ?; rewrite /floor -(@ltrz0 R) RtointK ?isint_Rfloor // Rfloor_lt0.
Qed.

End FloorTheory.

Section CeilTheory.
Variable R : realType.

Implicit Types x y : R.

Lemma isint_Rceil x : Rceil x \is a Rint.
Proof. by rewrite /Rceil rpredN isint_Rfloor. Qed.

Lemma Rceil0 : Rceil 0 = 0 :> R.
Proof. by rewrite /Rceil oppr0 Rfloor0 oppr0. Qed.

Lemma le_Rceil x : x <= Rceil x.
Proof. by rewrite /Rceil ler_oppr ge_Rfloor. Qed.

Lemma Rceil_le : {homo (@Rceil R) : x y / x <= y}.
Proof.
by move=> x y ?; rewrite /Rceil ler_oppl opprK Rfloor_le // ler_oppl opprK.
Qed.

Lemma Rceil_ge0 x : 0 <= x -> 0 <= Rceil x.
Proof. by move=> ?; rewrite -Rceil0 Rceil_le. Qed.

Lemma RceilE x : Rceil x = (ceil x)%:~R.
Proof. by rewrite /Rceil /ceil RfloorE mulrNz. Qed.

Lemma ceil_ge0 x : 0 <= x -> 0 <= ceil x.
Proof. by move=> ?; rewrite -(@ler_int R) -RceilE Rceil_ge0. Qed.

Lemma ceil_gt0 x : 0 < x -> 0 < ceil x.
Proof. by move=> ?; rewrite /ceil oppr_gt0 floor_lt0 // ltr_oppl oppr0. Qed.

Lemma ceil_le0 x : x <= 0 -> ceil x <= 0.
Proof. by move=> x0; rewrite -ler_oppl oppr0 floor_ge0 -ler_oppr oppr0. Qed.

Lemma ler_ceil x : x <= (ceil x)%:~R.
Proof. by rewrite -RceilE; exact: le_Rceil. Qed.

End CeilTheory.

(* -------------------------------------------------------------------- *)
Section Sup.
Context {R : realType}.

Lemma le_down (S : set R) : S `<=` down S.
Proof. by move=> x xS; apply/downP; exists x. Qed.

Lemma downK (S : set R) : down (down S) = down S.
Proof.
rewrite predeqE => x; split.
- case/downP => y /downP[z Sz yz xy].
  by apply/downP; exists z => //; rewrite (le_trans xy).
- by move=> Sx; apply/downP; exists x.
Qed.

Lemma has_sup_down (S : set R) : has_sup (down S) <-> has_sup S.
Proof.
split=> -[nzS nzubS].
  case: nzS=> x /downP[y yS le_xy]; split; first by exists y.
  case: nzubS=> u /ubP ubS; exists u; apply/ubP=> z zS.
  by apply/ubS; apply/downP; exists z.
case: nzS=> x xS; split; first by exists x; apply/le_down.
case: nzubS=> u /ubP ubS; exists u; apply/ubP=> y /downP [].
by move=> z zS /le_trans; apply; apply/ubS.
Qed.

Lemma le_sup (S1 S2 : set R) :
  S1 `<=` down S2 -> nonempty S1 -> has_sup S2
    -> sup S1 <= sup S2.
Proof.
move=> le_S12 nz_S1 hs_S2; have hs_S1: has_sup S1.
  split=> //; case: hs_S2=> _ [x ubx].
  exists x; apply/ubP=> y /le_S12 /downP[z zS2 le_yz].
  by apply/(le_trans le_yz); move/ubP: ubx; apply.
rewrite leNgt -subr_gt0; apply/negP => lt_sup.
case: (sup_adherent hs_S1 lt_sup)=> x /le_S12 xdS2.
rewrite subKr => lt_S2x; case/downP: xdS2=> z zS2.
move/(lt_le_trans lt_S2x); rewrite ltNge.
by move/ubP: (sup_upper_bound hs_S2) => ->.
Qed.

Lemma sup_down (S : set R) : sup (down S) = sup S.
Proof.
have [supS|supNS] := pselect (has_sup S); last first.
  by rewrite !sup_out // => /has_sup_down.
have supDS : has_sup (down S) by apply/has_sup_down.
apply/eqP; rewrite eq_le !le_sup //.
  by case: supS => -[x xS] _; exists x; apply/le_down.
  rewrite downK; exact: le_down.
  by case: supS.
Qed.

Lemma sup1 (c : R) : sup [set c] = c.
Proof.
have hs : has_sup [set c] by split; [exists c | exact: has_ub_set1].
apply/eqP; rewrite eq_le; move/ubP: (sup_upper_bound hs) => -> //.
by rewrite andbT; apply/sup_le_ub; [exists c | rewrite ub_set1].
Qed.

Lemma inf1 (c : R) : inf [set c] = c.
Proof.
rewrite /inf (_ : -%R @` (set1 c) = set1 (- c)).
by rewrite predeqE => x; split => [[y <- <-] //|->]; exists c.
by rewrite sup1 opprK.
Qed.

Lemma lt_sup_imfset {T : Type} (F : T -> R) l :
  has_sup [set y | exists x, y = F x] ->
  l < sup [set y | exists x, y = F x] ->
  exists2 x, l < F x & F x <= sup [set y | exists x, y = F x].
Proof.
set P := [set y | _]; move=> hs; rewrite -subr_gt0.
case/(sup_adherent hs) => _[x ->]; rewrite subKr=> lt_lFx.
by exists x => //; move/ubP : (sup_upper_bound hs) => -> //; exists x.
Qed.

Lemma lt_inf_imfset {T : Type} (F : T -> R) l :
  has_inf [set y | exists x, y = F x] ->
  inf [set y | exists x, y = F x] < l ->
  exists2 x, F x < l & inf [set y | exists x, y = F x] <= F x.
Proof.
set P := [set y | _]; move=> hs; rewrite -subr_gt0.
case/(inf_adherent hs)=> _ [x ->]; rewrite addrA [_ + l]addrC addrK.
by move=> ltFxl; exists x=> //; move/lbP : (inf_lower_bound hs) => -> //; exists x.
Qed.

End Sup.
