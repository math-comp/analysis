Require Import Reals.
From Coq Require Import ssreflect ssrfun ssrbool.
Require Import Rcomplements Rbar Markov Iter Lub.
From mathcomp Require Import ssrnat eqtype choice ssralg ssrnum.
From SsrReals Require Import boolp.
Require Import Rstruct.

(** ADD HEADER HERE !! *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.

(* Enrico's trick for tc resolution in have *)
Notation "!! x" := (ltac:(refine x)) (at level 100, only parsing).

Hint Resolve cond_pos.
Definition PosReal (x : R) (p : 0 < x) := mkposreal x (RltP _ _ p).

Section PosReal.
Implicit Types x y : posreal.

Lemma posreal_gt0 x : x > 0 :> R. Proof. by apply/RltP. Qed.
Hint Resolve posreal_gt0.
Lemma posreal_ge0 x : x >= 0 :> R. Proof. by apply: ltrW. Qed.
Hint Resolve posreal_ge0.
Lemma posreal_eq0 x : (x == 0 :> R) = false. Proof. by rewrite gtr_eqF. Qed.
Lemma posreal_neq0 x : (x != 0 :> R). Proof. by rewrite gtr_eqF. Qed.
Hint Resolve posreal_neq0.
Lemma posreal_le0 x : (x <= 0 :> R) = false.
Proof. by rewrite lerNgt posreal_gt0. Qed.
Lemma posreal_lt0 x : (x < 0 :> R) = false.
Proof. by rewrite ltrNge posreal_ge0. Qed.

Lemma min_pos_gt0 x y : 0 < minr (x : R) (y : R).
Proof. by rewrite ltr_minr !posreal_gt0. Qed.
Canonical minr_posreal x y := PosReal (@min_pos_gt0 x y).

Lemma add_pos_gt0 x y : 0 < (x : R) + (y : R).
Proof. by rewrite addr_gt0. Qed.
Canonical addr_posreal x y := PosReal (add_pos_gt0 x y).

Lemma mul_pos_posreal x y : 0 < (x : R) * (y : R).
Proof. by rewrite mulr_gt0. Qed.
Canonical mulr_posreal x y := PosReal (mul_pos_posreal x y).

Lemma muln_pos_posreal x n : 0 < (x : R) *+ n.+1.
Proof. by rewrite pmulrn_lgt0. Qed.
Canonical mulrn_posreal x n := PosReal (muln_pos_posreal x n).

Lemma inv_pos_gt0 x : 0 < (x : R)^-1. Proof. by rewrite invr_gt0. Qed.
Canonical invr_posreal x := PosReal (inv_pos_gt0 x).

Lemma one_pos_gt0 : 0 < 1 :> R. Proof. by rewrite ltr01. Qed.
Canonical oner_posreal := PosReal (@ltr01 _).

Definition posreal_of (x : R) y of x = y := y.
End PosReal.

Hint Resolve posreal_gt0.
Hint Resolve posreal_ge0.
Hint Resolve posreal_neq0.
Notation "[ 'posreal' 'of' x ]" := (@posreal_of x _ erefl)
  (format "[ 'posreal'  'of'  x ]") : ring_scope.

Definition dep_arrow_eq (T : eqType) (T' : T -> eqType)
   (f g : forall x : T, T' x) := `[<f = g>].
Lemma dep_arrow_eqP (T : eqType) (T' : T -> eqType) : Equality.axiom (@dep_arrow_eq T T').
Proof.
by move=> f g; apply: (iffP idP) => [/asboolP|->]; last by apply/asboolP.
Qed.

Definition dep_arrow_eqMixin (T : eqType) (T' : T -> eqType) := EqMixin (@dep_arrow_eqP T T').
Definition dep_arrow_eqType  (T : eqType) (T' : T -> eqType) :=
  EqType (forall x : T, T' x) (@dep_arrow_eqMixin T T').
Canonical arrow_eqType (T : eqType) (T' : eqType) :=
  EqType (T -> T') (@dep_arrow_eqMixin T _).

Axiom arrow_choiceMixin : forall T T' : Type, Choice.mixin_of (T -> T').
Canonical arrow_choiceType (T : choiceType) (T' : choiceType) :=
  ChoiceType (T -> T') (@arrow_choiceMixin T T').

Reserved Notation "A `&` B"  (at level 48, left associativity).
Reserved Notation "A `*` B"  (at level 46, left associativity).
Reserved Notation "A `+` B"  (at level 54, left associativity).
Reserved Notation "A +` B"  (at level 54, left associativity).
Reserved Notation "A `|` B" (at level 52, left associativity).
Reserved Notation "a |` A" (at level 52, left associativity).
Reserved Notation "A `\` B" (at level 50, left associativity).
Reserved Notation "A `\ b" (at level 50, left associativity).

Definition set A := A -> Prop.
Definition in_set T (P : set T) : pred T := [pred x | `[<P x>]].
Canonical set_predType T := @mkPredType T (set T) (@in_set T).

Lemma in_setE T (P : set T) x : x \in P = P x :> Prop.
Proof. by rewrite propeqE; split => [] /asboolP. Qed.

Bind Scope classical_set_scope with set.
Local Open Scope classical_set_scope.

Notation "[ 'set' x : T | P ]" := ((fun x => P) : set T)
  (at level 0, x at level 99, only parsing) : classical_set_scope.
Notation "[ 'set' x | P ]" := [set x : _ | P]
  (at level 0, x, P at level 99, format "[ 'set'  x  |  P ]") : classical_set_scope.

Notation "[ 'set' E | x 'in' A ]" := [set y | exists2 x, A x & E = y]
  (at level 0, E, x at level 99,
   format "[ '[hv' 'set'  E '/ '  |  x  'in'  A ] ']'") : classical_set_scope.

Definition image {A B} (f : A -> B) (X : set A) : set B :=
  [set f a | a in X].

Definition preimage {A B} (f : A -> B) (X : set B) : set A := [set a | X (f a)].
Arguments preimage A B f X / a.

Definition setT {A} := [set _ : A | True].
Definition set0 {A} := [set _ : A | False].
Definition set1 {A} (x : A) := [set a : A | a = x].
Definition setI {A} (X Y : set A) := [set a | X a /\ Y a].
Definition setU {A} (X Y : set A) := [set a | X a \/ Y a].
Definition nonempty {A} (X : set A) := exists x, X x.
Definition setC {A} (X : set A) := [set a | ~ X a].
Definition setD {A} (X Y : set A) := [set a | X a /\ ~ Y a].

Notation "[ 'set' a ]" := (set1 a)
  (at level 0, a at level 99, format "[ 'set'  a ]") : classical_set_scope.
Notation "[ 'set' a : T ]" := [set (a : T)]
  (at level 0, a at level 99, format "[ 'set'  a   :  T ]") : classical_set_scope.
Notation "A `|` B" := (setU A B) : classical_set_scope.
Notation "a |` A" := ([set a] `|` A) : classical_set_scope.
Notation "[ 'set' a1 ; a2 ; .. ; an ]" := (setU .. (a1 |` [set a2]) .. [set an])
  (at level 0, a1 at level 99,
   format "[ 'set'  a1 ;  a2 ;  .. ;  an ]") : classical_set_scope.
Notation "A `&` B" := (setI A B) : classical_set_scope.
Notation "~` A" := (setC A) (at level 35, right associativity) : classical_set_scope.
Notation "[ 'set' ~ a ]" := (~` [set a])
  (at level 0, format "[ 'set' ~  a ]") : classical_set_scope.
Notation "A `\` B" := (setD A B) : classical_set_scope.
Notation "A `\ a" := (A `\` [set a]) : classical_set_scope.

Definition bigsetI A I (P : set I) (X : I -> set A) :=
  [set a | forall i, P i -> X i a].
Definition bigsetU A I (P : set I) (X : I -> set A) :=
  [set a | exists2 i, P i & X i a].

Notation "\bigcup_ ( i 'in' P ) F" :=
  (bigsetU P (fun i => F))
  (at level 41, F at level 41, i, P at level 50,
           format "'[' \bigcup_ ( i  'in'  P ) '/  '  F ']'")
 : classical_set_scope.
Notation "\bigcup_ ( i : T ) F" :=
  (\bigcup_(i in @setT T) F)
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcup_ ( i  :  T ) '/  '  F ']'")
 : classical_set_scope.
Notation "\bigcup_ i F" :=
  (\bigcup_(i : _) F)
  (at level 41, F at level 41, i at level 0,
           format "'[' \bigcup_ i '/  '  F ']'")
 : classical_set_scope.

Notation "\bigcap_ ( i 'in' P ) F" :=
  (bigsetI P (fun i => F))
  (at level 41, F at level 41, i, P at level 50,
           format "'[' \bigcap_ ( i  'in'  P ) '/  '  F ']'")
 : classical_set_scope.
Notation "\bigcap_ ( i : T ) F" :=
  (\bigcap_(i in @setT T) F)
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcap_ ( i  :  T ) '/  '  F ']'")
 : classical_set_scope.
Notation "\bigcap_ i F" :=
  (\bigcap_(i : _) F)
  (at level 41, F at level 41, i at level 0,
           format "'[' \bigcap_ i '/  '  F ']'")
 : classical_set_scope.

Definition subset {A} (X Y : set A) := forall a, X a -> Y a.

Notation "A `<=` B" := (subset A B) (at level 70, no associativity)
 : classical_set_scope.
Notation "f @^-1` A" := (preimage f A) (at level 24) : classical_set_scope.
Notation "f @` A" := (image f A) (at level 24) : classical_set_scope.
Notation "A !=set0" := (nonempty A) (at level 80) : classical_set_scope.

Lemma imageP {A B} (f : A -> B) (X : set A) a : X a -> (f @` X) (f a).
Proof. by exists a. Qed.

Lemma sub_image_setI {A B} (f : A -> B) (X Y : set A) :
  f @` (X `&` Y) `<=` f @` X `&` f @` Y.
Proof. by move=> b [x [Xa Ya <-]]; split; apply: imageP. Qed.
Arguments sub_image_setI {A B f X Y} a _.

Lemma nonempty_image {A B} (f : A -> B) (X : set A) :
  f @` X !=set0 -> X !=set0.
Proof. by case=> b [a]; exists a. Qed.

Lemma nonempty_preimage {A B} (f : A -> B) (X : set B) :
  f @^-1` X !=set0 -> X !=set0.
Proof. by case=> [a ?]; exists (f a). Qed.

Lemma subset_empty {A} (X Y : set A) : X `<=` Y -> X !=set0 -> Y !=set0.
Proof. by move=> sXY [x Xx]; exists x; apply: sXY. Qed.

Lemma subset_trans {A} (Y X Z : set A) : X `<=` Y -> Y `<=` Z -> X `<=` Z.
Proof. by move=> sXY sYZ ? ?; apply/sYZ/sXY. Qed.

Lemma nonempty_preimage_setI {A B} (f : A -> B) (X Y : set B) :
  (f @^-1` (X `&` Y)) !=set0 <-> (f @^-1` X `&` f @^-1` Y) !=set0.
Proof. by split; case=> x ?; exists x. Qed.

Lemma subsetC {A} (X Y : set A) : X `<=` Y -> ~` Y `<=` ~` X.
Proof. by move=> sXY ? nYa ?; apply/nYa/sXY. Qed.

Lemma subsetU {A} (X Y Z : set A) : X `<=` Z -> Y `<=` Z -> X `|` Y `<=` Z.
Proof. by move=> sXZ sYZ a; apply: or_ind; [apply: sXZ|apply: sYZ]. Qed.

Lemma setDE {A} (X Y : set A) : X `\` Y = X `&` ~` Y.
Proof. by []. Qed.

(* Index the filter (2nd proj) on a term (1st proj) *)
Structure canonical_filter_on X Y := CanonicalFilterOn {
  canonical_filter_term : X;
  _ : set (set Y)
}.
(* Defining the 2nd proj, not named before to prevent Warnings *)
(* when adding a canonical instance of canonical_filter_on *)
Definition canonical_term_filter {X Y} (F : canonical_filter_on X Y) :=
  let: CanonicalFilterOn x f := F in f.
(* Coercion canonical_term_filter : canonical_filter_on >-> set. *)
(* Identity Coercion set >-> Funclass. *)

(* Index a family of filters on a type, one for each element of the type *)
Structure canonical_filter Y := CanonicalFilter {
  canonical_filter_type :> Type;
  _ : canonical_filter_type -> set (set Y)
}.
(* Naming the second proj *)
Definition canonical_type_filter {Y} {F : canonical_filter Y} :
  F -> set (set Y) :=
  let: CanonicalFilter X f := F in f.

(* The default filter for an arbitrary element is the one obtained *)
(* from its type *)
Canonical default_filter_term Y (X : canonical_filter Y) (x : X) :=
  @CanonicalFilterOn X Y x (canonical_type_filter x).

(* filter on arrow sources *)
Structure canonical_filter_source Z Y := CanonicalFilterSource {
  canonical_filter_source_type :> Type;
  _ : (canonical_filter_source_type -> Z) -> set (set Y)
}.
Definition canonical_source_filter Z Y (F : canonical_filter_source Z Y) :
  (F -> Z) -> set (set Y) :=
  let: CanonicalFilterSource X f := F in f.

Canonical default_arrow_filter Y Z (X : canonical_filter_source Z Y) :=
  @CanonicalFilter _ (X -> Z) (@canonical_source_filter _ _ X).

Canonical source_filter_filter Y :=
  @CanonicalFilterSource Prop _ (_ -> Prop) (fun x : (set (set Y)) => x).
Canonical source_filter_filter' Y :=
  @CanonicalFilterSource Prop _ (set _) (fun x : (set (set Y)) => x).

Definition filter_of X Y (F : canonical_filter_on X Y)
  (x : X) (_ : x = canonical_filter_term F) :=
  canonical_term_filter F.

Notation "[ 'filter' 'of' x ]" := (@filter_of _ _ _ x erefl)
  (format "[ 'filter'  'of'  x ]").
Arguments filter_of _ _ _ _ _ _ /.

Lemma filter_ofE  T (F : set (set T)) : [filter of F] = F.
Proof. by []. Qed.

Open Scope R_scope.

(** * Filters *)

(** ** Definitions *)

Class Filter {T : Type} (F : set (set T)) := {
  filter_true : F setT ;
  filter_and : forall P Q : set T, F P -> F Q -> F (P `&` Q) ;
  filter_imp : forall P Q : set T, P `<=` Q -> F P -> F Q
}.
Global Hint Mode Filter - ! : typeclass_instances.

Class ProperFilter' {T : Type} (F : set (set T)) := {
  filter_not_empty : not (F (fun _ => False)) ;
  filter_filter' :> Filter F
}.
Global Hint Mode ProperFilter' - ! : typeclass_instances.
Arguments filter_not_empty {T} F {_}.

Notation ProperFilter := ProperFilter'.

Lemma filter_not_empty_ex {T : Type} (F : set (set T)) :
    (forall P, F P -> exists x, P x) -> ~ F set0.
Proof. by move=> /(_ set0) ex /ex []. Qed.

Definition Build_ProperFilter {T : Type} (F : set (set T))
  (filter_ex : forall P, F P -> exists x, P x)
  (filter_filter : Filter F) :=
  Build_ProperFilter' (filter_not_empty_ex filter_ex) (filter_filter).

Lemma filter_ex_subproof {T : Type} (F : set (set T)) :
     ~ F set0 -> (forall P, F P -> exists x, P x).
Proof.
move=> NFset0 P FP; apply: contrapNT NFset0 => nex; suff <- : P = set0 by [].
by rewrite funeqE => x; rewrite propeqE; split=> // Px; apply: nex; exists x.
Qed.

Definition filter_ex {T : Type} (F : set (set T)) {FF : ProperFilter F} :=
  filter_ex_subproof (filter_not_empty F).
Arguments filter_ex {T F FF _}.

Lemma filterP T (F : set (set T)) {FF : Filter F} (P : set T) :
  (exists2 Q : set T, F Q & forall x, Q x -> P x) <-> F P.
Proof.
split; last by exists P.
by move=> [Q FQ QP]; apply: (filter_imp QP).
Qed.

Lemma filter_forall {T : Type} {F} {FF: @Filter T F} (P : T -> Prop) :
  (forall x, P x) -> F P.
Proof. by move=> ?; apply/filterP; exists setT => //; apply: filter_true. Qed.

Lemma filter_const {T : Type} {F} {FF: @ProperFilter T F} (P : Prop) :
  F (fun=> P) -> P.
Proof. by move=> FP; case: (filter_ex FP). Qed.

(** ** Limits expressed with filters *)

Definition filter_le {T : Type} (F G : set (set T)) := G `<=` F.

Notation "F --> G" := (filter_le [filter of F] [filter of G])
  (at level 70, format "F  -->  G") : classical_set_scope.

Lemma filter_le_refl T (F : set (set T)) : F --> F.
Proof. exact. Qed.

Lemma filter_le_trans T (F G H : set (set T)) :
  (F --> G) -> (G --> H) -> (F --> H).
Proof. by move=> FG GH P /GH /FG. Qed.

Definition filtermap {T U : Type} (f : T -> U) (F : set (set T)) :=
  [set P | F (f @^-1` P)].

Lemma filtermapE {U V : Type} (f : U -> V)
  (F : set (set U)) (P : set V) : filtermap f F P = F (f @^-1` P).
Proof. by []. Qed.

Notation "E @[ x --> F ]" := (filtermap (fun x => E) [filter of F])
  (at level 60, x ident, format "E  @[ x  -->  F ]") : classical_set_scope.
Notation "f @ F" := (filtermap f [filter of F])
  (at level 60, format "f  @  F") : classical_set_scope.

Global Instance filtermap_filter T U (f : T -> U) (F : set (set T)) :
  Filter F -> Filter (f @ F).
Proof.
move=> FF; constructor => [|P Q|P Q PQ]; rewrite ?filtermapE ?filter_ofE //=.
- exact: filter_true.
- exact: filter_and.
- by apply: filter_imp=> ?/PQ.
Qed.

Global Instance filtermap_proper_filter T U (f : T -> U) (F : set (set T)) :
  ProperFilter F -> ProperFilter (f @ F).
Proof.
move=> FF; apply: Build_ProperFilter';
by rewrite filtermapE; apply: filter_not_empty.
Qed.
Definition filtermap_proper_filter' := filtermap_proper_filter.

Definition filtermapi {T U : Type} (f : T -> set U) (F : set (set T)) :=
  [set P | F [set x | exists y, f x y /\ P y]].

Notation "E `@[ x --> F ]" := (filtermapi (fun x => E) F)
  (at level 60, x ident, format "E  `@[ x  -->  F ]") : classical_set_scope.
Notation "f `@ F" := (filtermapi f [filter of F])
  (at level 60, format "f  `@  F") : classical_set_scope.

Lemma filtermapiE {U V : Type} (f : U -> set V)
  (F : set (set U)) (P : set V) : filtermapi f F P = F [set x | exists y, f x y /\ P y].
Proof. by []. Qed.

Global Instance filtermapi_filter T U (f : T -> U -> Prop) (F : set (set T)) :
  F [set x | (exists y, f x y) /\ forall y1 y2, f x y1 -> f x y2 -> y1 = y2] ->
  Filter F -> Filter (f `@ F).
Proof.
move=> FP FF; rewrite /filtermapi; apply: Build_Filter.
- apply: filter_imp FP => x [[y Hy] H].
  exists y.
  exact (conj Hy I).
- intros P Q HP HQ.
  apply: filter_imp (filter_and (filter_and HP HQ) FP).
  intros x [[[y1 [Hy1 Py]] [y2 [Hy2 Qy]]] [[y Hy] Hf]].
  exists y.
  apply (conj Hy).
  split.
  now rewrite (Hf y y1).
  now rewrite (Hf y y2).
- intros P Q HPQ HP.
  apply: filter_imp HP.
  intros x [y [Hf Py]].
  exists y.
  apply (conj Hf).
  now apply HPQ.
Qed.

Global Instance filtermapi_proper_filter
  T U (f : T -> U -> Prop) (F : set (set T)) :
  F [set x | (exists y, f x y) /\ forall y1 y2, f x y1 -> f x y2 -> y1 = y2] ->
  ProperFilter F -> ProperFilter (f `@ F).
Proof.
intros HF FF.
unfold filtermapi.
split.
- intro H.
  apply: filter_not_empty.
  apply filter_imp with (2 := H).
  now intros x [y [_ Hy]].
- apply filtermapi_filter.
  exact HF.
  apply filter_filter'.
Qed.
Definition filter_map_proper_filter' := filtermapi_proper_filter.

Lemma filterlim_id T (F : set (set T)) : x @[x --> F] --> F.
Proof. exact. Qed.

Lemma filterlim_comp T U V (f : T -> U) (g : U -> V)
  (F : set (set T)) (G : set (set U)) (H : set (set V)) :
  f @ F --> G -> g @ G --> H -> g (f x) @[x --> F] --> H.
Proof.
intros FG GH P HP.
apply (FG (fun x => P (g x))).
now apply GH.
Qed.

Lemma filterlim_ext_loc {T U} {F : set (set T)} {G : set (set U)}
  {FF : Filter F} (f g : T -> U) :
  F (fun x => f x = g x) -> f @ F --> G -> g @ F --> G.
Proof.
intros  Efg Lf P GP.
specialize (Lf P GP).
generalize (@filter_and _ _ _ _ (fun x : T => P (f x)) Efg Lf).
apply: filter_imp.
now intros x [-> H].
Qed.

Lemma filterlim_ext {T U} {F : set (set T)} {G : set (set U)}
  {FF : Filter F} (f g : T -> U) :
  (forall x, f x = g x) -> f @ F --> G -> g @ F --> G.
Proof.
intros Efg.
apply filterlim_ext_loc.
now apply filter_forall.
Qed.

Lemma filterlim_trans {T} {F G H : set (set T)} : F --> G -> G --> H -> F --> H.
Proof. by move=> FG GH P /GH /FG. Qed.

Lemma filterlim_filter_le_1 {T U} {F G : set (set T)} {H : set (set U)}
  (f : T -> U) : G --> F -> f @ F --> H -> f @ G --> H.
Proof.
intros K Hf P HP.
apply K.
now apply Hf.
Qed.

Lemma filterlim_filter_le_2 {T U} {F : set (set T)} {G H : set (set U)}
  (f : T -> U) : G --> H -> f @ F --> G -> f @ F --> H.
Proof.
intros K Hf P HP.
apply Hf.
now apply K.
Qed.

Lemma filterlimi_comp T U V (f : T -> U) (g : U -> set V)
  (F : set (set T)) (G : set (set U)) (H : set (set V)) :
  f @ F --> G -> g `@ G --> H -> g (f x) `@[x --> F] --> H.
Proof.
intros FG GH P HP.
apply (FG (fun x => exists y, g x y /\ P y)).
now apply GH.
Qed.

Lemma filterlimi_ext_loc {T U} {F : set (set T)} {G : set (set U)}
  {FF : Filter F} (f g : T -> set U) :
  F [set x : T | forall y, f x y <-> g x y] ->
  f `@ F --> G -> g `@ F --> G.
Proof.
intros Efg Lf P GP.
specialize (Lf P GP).
generalize (filter_and Efg Lf).
apply: filter_imp.
intros x [H [y [Hy1 Hy2]]].
exists y.
apply: conj Hy2.
now apply H.
Qed.

Lemma filterlimi_ext  {T U} {F : set (set T)} {G : set (set U)}
  {FF : Filter F} (f g : T -> set U) :
  (forall x y, f x y <-> g x y) ->
  f `@ F --> G -> g `@ F --> G.
Proof.
intros Efg.
apply filterlimi_ext_loc.
now apply filter_forall.
Qed.

Lemma filterlimi_filter_le_1 {T U} {F G : set (set T)} {H : set (set U)}
  (f : T -> set U) : G --> F -> f `@ F --> H -> f `@ G --> H.
Proof.
intros K Hf P HP.
apply K.
now apply Hf.
Qed.

Lemma filterlimi_filter_le_2  {T U} {F : set (set T)} {G H : set (set U)}
  (f : T -> set U) : G --> H -> f `@ F --> G -> f `@ F --> H.
Proof.
intros K Hf P HP.
apply Hf.
now apply K.
Qed.

(** ** Specific filters *)

(** Filters for pairs *)

Inductive filter_prod {T U : Type} (F G : _ -> Prop) (P : T * U -> Prop) : Prop :=
  Filter_prod (Q : T -> Prop) (R : U -> Prop) :
    F Q -> G R -> (forall x y, Q x -> R y -> P (x, y)) -> filter_prod F G P.

Definition apply_filter_prod {X1 X2 Y1 Y2} (f : Y1 -> set (set X1))
  (g : Y2 -> set (set X2)) (y1 : Y1) (y2 : Y2) : set (set (X1 * X2)) :=
  filter_prod (f y1) (g y2).

Canonical canonical_filter_prod X1 X2 (Z1 : canonical_filter X1)
  (Z2 : canonical_filter X2) : canonical_filter (X1 * X2) :=
  @CanonicalFilter _ _ (fun x => apply_filter_prod
  (@canonical_type_filter _ Z1) (@canonical_type_filter _ Z2) x.1 x.2).

Global Instance filter_prod_filter :
  forall T U (F : set (set T)) (G : set (set U)),
  Filter F -> Filter G -> Filter (filter_prod F G).
Proof.
intros T U F G FF FG.
constructor.
- exists (fun _ => True) (fun _ => True).
  apply filter_true.
  apply filter_true.
  easy.
- intros P Q [AP BP P1 P2 P3] [AQ BQ Q1 Q2 Q3].
  exists (fun x => AP x /\ AQ x) (fun x => BP x /\ BQ x).
  now apply filter_and.
  now apply filter_and.
  intros x y [Px Qx] [Py Qy].
  split.
  now apply P3.
  now apply Q3.
- intros P Q HI [AP BP P1 P2 P3].
  exists AP BP ; try easy.
  intros x y Hx Hy.
  apply HI.
  now apply P3.
Qed.

Global Instance filter_prod_proper {T1 T2 : Type}
  {F : (T1 -> Prop) -> Prop} {G : (T2 -> Prop) -> Prop}
  {FF : ProperFilter F} {FG : ProperFilter G} :
  ProperFilter (filter_prod F G).
Proof.
apply: Build_ProperFilter'.
apply: filter_prod_ind => Q R FQ GR QRF.
apply: (filter_not_empty F); apply: filter_imp FQ => x Qx.
apply: (filter_not_empty G); apply: filter_imp GR => y Ry.
exact: QRF Qx Ry.
Qed.
Definition filter_prod_proper' := @filter_prod_proper.

Lemma filterlim_fst {T U F G} {FG : Filter G} :
  (@fst T U) @ filter_prod F G --> F.
Proof.
intros P HP.
exists P (fun _ => True) ; try easy.
apply filter_true.
Qed.

Lemma filterlim_snd {T U F G} {FF : Filter F} :
  (@snd T U) @ filter_prod F G --> G.
Proof.
intros P HP.
exists (fun _ => True) P ; try easy.
apply filter_true.
Qed.

Lemma filterlim_pair {T U V F G H} {FF : Filter F} (f : T -> U) (g : T -> V) :
  f @ F --> G -> g @ F --> H ->
  (f x, g x) @[x --> F] --> filter_prod G H.
Proof.
intros Cf Cg P [A B GA HB HP].
unfold filtermap.
apply: (@filter_imp _ _ _ (fun x => A (f x) /\ B (g x))).
intros x [Af Bg].
now apply HP.
apply filter_and.
now apply Cf.
now apply Cg.
Qed.

Lemma filterlim_comp_2 {T U V W}
  {F : set (set T)} {G : set (set U)} {H : set (set V)} {I : set (set W)}
  {FF : Filter F}
  (f : T -> U) (g : T -> V) (h : U -> V -> W) :
  f @ F --> G -> g @ F --> H ->
  h (fst x) (snd x) @[x --> (G, H)] --> I ->
  h (f x) (g x) @[x --> F] --> I.
Proof.
intros Cf Cg Ch.
change (fun x => h (f x) (g x)) with (fun x => h (fst (f x, g x)) (snd (f x, g x))).
apply: filterlim_comp Ch.
now apply filterlim_pair.
Qed.

Lemma filterlimi_comp_2 {T U V W F G H} {I : set (set W)} {FF : Filter F}
  (f : T -> U) (g : T -> V) (h : U -> V -> set W) :
  f @ F --> G -> g @ F --> H ->
  h (fst x) (snd x) `@[x --> filter_prod G H] --> I ->
  h (f x) (g x) `@[x --> F] --> I.
Proof.
intros Cf Cg Ch.
change (fun x => h (f x) (g x)) with (fun x => h (fst (f x, g x)) (snd (f x, g x))).
apply: filterlimi_comp Ch.
now apply filterlim_pair.
Qed.

(** Restriction of a filter to a domain *)

Definition within {T : Type} D (F : set (set T)) (P : T -> Prop) :=
  F [set x | D x -> P x].

Global Instance within_filter :
  forall T D F, Filter F -> Filter (@within T D F).
Proof.
intros T D F FF.
unfold within.
constructor.
- now apply filter_forall.
- intros P Q WP WQ.
  apply filter_imp with (fun x => (D x -> P x) /\ (D x -> Q x)).
  intros x [HP HQ] HD.
  split.
  now apply HP.
  now apply HQ.
  now apply filter_and.
- intros P Q H FP.
  apply filter_imp with (fun x => (D x -> P x) /\ (P x -> Q x)).
  intros x [H1 H2] HD.
  apply H2, H1, HD.
  apply filter_and.
  exact FP.
  now apply filter_forall.
Qed.

Lemma filter_le_within {T} {F : set (set T)} {FF : Filter F} D :
  within D F --> F.
Proof.
now intros P; apply: filter_imp.
Qed.

Lemma filterlim_within_ext {T U F} {G : set (set U)}
  {FF : Filter F} D (f g : T -> U) :
  (forall x, D x -> f x = g x) ->
  f @ within D F --> G ->
  g @ within D F --> G.
Proof.
intros Efg.
apply filterlim_ext_loc.
unfold within.
now apply filter_forall.
Qed.

Definition subset_filter {T} (F : set (set T))
  (dom : T -> Prop) (P : {x|dom x} -> Prop) : Prop :=
  F [set x | forall H : dom x, P (exist _ x H)].
Arguments subset_filter {T} F dom _.

Global Instance subset_filter_filter T F (dom : T -> Prop) :
  Filter F -> Filter (subset_filter F dom).
Proof.
move=> FF.
constructor ; unfold subset_filter.
- now apply filter_imp with (2 := filter_true).
- intros P Q HP HQ.
  generalize (filter_and HP HQ).
  apply filter_imp.
  intros x [H1 H2] H.
  now split.
- intros P Q H.
  apply filter_imp.
  intros x H' H0.
  now apply H.
Qed.

Lemma subset_filter_proper {T F} {FF : Filter F} (dom : T -> Prop) :
  (forall P, F P -> ~ ~ exists x, dom x /\ P x) ->
  ProperFilter (subset_filter F dom).
Proof.
move=> domAP; apply: Build_ProperFilter'; rewrite /subset_filter => subF_dom.
by have /(_ subF_dom) := domAP (~` dom); apply => -[x [dx /(_ dx)]].
Qed.
Definition subset_filter_proper' := @subset_filter_proper.

(** * Uniform spaces defined using balls *)

Module Uniform.

Record mixin_of (M : Type) := Mixin {
  point : M ;
  ball : M -> R -> M -> Prop ;
  ax1 : forall x (e : posreal), ball x e x ;
  ax2 : forall x y (e : R), ball x e y -> ball y e x ;
  ax3 : forall x y z e1 e2, ball x e1 y -> ball y e2 z -> ball x (e1 + e2) z
}.

Record class_of (M : Type) := Class {
  base : Choice.class_of M;
  mixin : mixin_of M
}.

Section ClassDef.

Structure type := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ := cT return class_of cT in c.

Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).
Local Coercion base : class_of >-> Choice.class_of.
Local Coercion mixin : class_of >-> mixin_of.

Definition pack m :=
  fun bT b of phant_id (Choice.class bT) b => @Pack T (Class b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.

End ClassDef.

Module Exports.

Coercion sort : type >-> Sortclass.
Coercion base : class_of >-> Choice.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Notation uniformType := type.
Notation UniformType T m := (@pack T m _ _ idfun).
Notation UniformMixin := Mixin.
Notation "[ 'uniformType' 'of' T 'for' cT ]" :=  (@clone T cT _ idfun)
  (at level 0, format "[ 'uniformType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'uniformType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'uniformType'  'of'  T ]") : form_scope.

End Exports.

End Uniform.

Export Uniform.Exports.

Definition point {M : uniformType} := Uniform.point (Uniform.class M).
Definition ball {M : uniformType} := Uniform.ball (Uniform.class M).
Definition locally {M : uniformType} : M -> set (set M) :=
  fun (x : M) P => exists eps : posreal, forall y, ball x eps y -> P y.
Definition uniformType_is_canonical_filter {M : uniformType} :=
   @CanonicalFilter M M locally.
Coercion uniformType_is_canonical_filter : uniformType >-> canonical_filter.
Canonical uniformType_is_canonical_filter.

(* move to boolP *)
Definition get {T : uniformType} (P : set T) : T :=
  if pselect (exists x : T, `[<P x>]) isn't left exP then point
  else projT1 (sigW exP).

(* Unique Choice for compatilibility reasons *)
Definition iota {T : uniformType} := @get T.

Lemma getPex {T : uniformType} (P : set T) : (exists x, P x) -> P (get P).
Proof.
rewrite /get; case: pselect => [|nexP [x Px]]; last first.
  by exfalso; apply: nexP; exists x; apply/asboolP.
by move=> p; case: sigW=> {p} /= x /asboolP.
Qed.

Lemma getP {T : uniformType} (P : set T) (x : T): P x -> P (get P).
Proof. by move=> Px; apply: getPex; exists x. Qed.

Lemma getPN {T : uniformType} (P : set T) : (forall x, ~ P x) -> get P = point.
Proof.
rewrite /get; case: pselect => //= - [x p /(_ x)].
by have /asboolP q := p => /(_ q).
Qed.

Definition lim {M : uniformType} (F : set (set M)) : M := get (fun x : M => F --> x).

Section uniformType1.
Context {M : uniformType}.

Lemma ball_center (x : M) (e : posreal) : ball x e x.
Proof. exact: Uniform.ax1. Qed.
Hint Resolve ball_center.

Lemma ballxx (x : M) (e : R) : (0 < e)%R -> ball x e x.
Proof. by move=> e_gt0; apply: ball_center (PosReal e_gt0). Qed.

Lemma ball_sym (x y : M) (e : R) : ball x e y -> ball y e x.
Proof. exact: Uniform.ax2. Qed.

Lemma ball_triangle (x y z : M) (e1 e2 : R) :
  ball x e1 y -> ball y e2 z -> ball x (e1 + e2) z.
Proof. exact: Uniform.ax3. Qed.

Lemma ball_ler (x : M) (e1 e2 : R) : (e1 <= e2)%R -> ball x e1 `<=` ball x e2.
Proof.
move=> le12 y; case: ltrgtP le12 => [//|lte12 _|->//].
by rewrite -[e2](subrK e1); apply/ball_triangle/ballxx; rewrite subr_gt0.
Qed.

Lemma ball_le (x : M) (e1 e2 : R) : e1 <= e2 -> ball x e1 `<=` ball x e2.
Proof. by move=> /RleP/ball_ler. Qed.

Definition close (x y : M) : Prop := forall eps : posreal, ball x eps y.

Lemma close_refl (x : M) : close x x. Proof. by []. Qed.

Lemma close_sym (x y : M) : close x y -> close y x.
Proof. by move=> ??; apply: ball_sym. Qed.

Lemma close_trans (x y z : M) : close x y -> close y z -> close x z.
Proof. by move=> ?? eps; rewrite (double_var eps); apply: ball_triangle. Qed.

End uniformType1.

Hint Resolve ball_center.
Hint Resolve close_refl.

(** ** Specific uniform spaces *)

(** Rings with absolute value *)


Section prod_Uniform.

Context {U V : uniformType}.
Implicit Types (x y : U * V).

Definition prod_point : U * V := (point, point).

Definition prod_ball x (eps : R) y :=
  ball (fst x) eps (fst y) /\ ball (snd x) eps (snd y).

Lemma prod_ball_center x (eps : posreal) : prod_ball x eps x.
Proof. by split. Qed.

Lemma prod_ball_sym x y (eps : R) : prod_ball x eps y -> prod_ball y eps x.
Proof. by move=> [bxy1 bxy2]; split; apply: ball_sym. Qed.

Lemma prod_ball_triangle x y z (e1 e2 : R) :
  prod_ball x e1 y -> prod_ball y e2 z -> prod_ball x (e1 + e2) z.
Proof.
by move=> [bxy1 bxy2] [byz1 byz2]; split; eapply ball_triangle; eassumption.
Qed.

End prod_Uniform.

Definition prod_uniformType_mixin (U V : uniformType) :=
  @Uniform.Mixin (U * V) prod_point _ prod_ball_center prod_ball_sym prod_ball_triangle.

Canonical prod_uniformType (U V : uniformType) :=
  UniformType (U * V) (prod_uniformType_mixin U V).

(** Functional metric spaces *)

Section fct_Uniform.

Variable (T : choiceType) (U : uniformType).

Definition fct_point : T -> U := fun=> point.

Definition fct_ball (x : T -> U) (eps : R) (y : T -> U) :=
  forall t : T, ball (x t) eps (y t).

Lemma fct_ball_center :
  forall (x : T -> U) (e : posreal),
  fct_ball x e x.
Proof.
  intros x e t.
  exact: ball_center.
Qed.

Lemma fct_ball_sym :
  forall (x y : T -> U) (e : R),
  fct_ball x e y -> fct_ball y e x.
Proof.
  intros x y e H t.
  exact: ball_sym.
Qed.

Lemma fct_ball_triangle :
  forall (x y z : T -> U) (e1 e2 : R),
  fct_ball x e1 y -> fct_ball y e2 z -> fct_ball x (e1 + e2) z.
Proof.
  intros x y z e1 e2 H1 H2 t.
  now apply ball_triangle with (y t).
Qed.

Definition fct_uniformType_mixin :=
  @Uniform.Mixin _ fct_point _ fct_ball_center fct_ball_sym fct_ball_triangle.

Canonical fct_uniformType := UniformType (T -> U) fct_uniformType_mixin.
Canonical generic_source_filter := @CanonicalFilterSource _ _ _ locally.

End fct_Uniform.

(** ** Local predicates *)
(** locally_dist *)

Definition locally_dist {T : Type} (d : T -> R) (P : T -> Prop) :=
  exists delta : posreal, forall y, d y < delta -> P y.

Global Instance locally_dist_filter :
  forall T (d : T -> R), Filter (locally_dist d).
Proof.
intros T d.
constructor.
- now exists [posreal of 1].
- intros P Q [dP HP] [dQ HQ].
  exists [posreal of (Rmin dP dQ)] => y /= Hy.
  split.
  apply HP.
  apply Rlt_le_trans with (1 := Hy).
  apply Rmin_l.
  apply HQ.
  apply Rlt_le_trans with (1 := Hy).
  apply Rmin_r.
- intros P Q H [dP HP].
  exists dP.
  intros y Hy.
  apply H.
  now apply HP.
Qed.

(** locally *)

(*Require Import FunctionalExtensionality.
Notation funext := functional_extensionality.*)

Section LocallyDef.

Context {T : uniformType}.
Implicit Types x y : T.

Global Instance locally_filter (x : T) : ProperFilter (locally x).
Proof.
constructor => [[eps /(_ _ (ball_center _ _))] //|].
constructor => [|P Q [dP xP] [dQ xQ]|P Q subPQ [dP xP]]; last 1 first.
- by exists dP => y /xP /subPQ.
- by exists [posreal of 1]%R.
pose m := [posreal of minr (dP : R) (dQ : R)]%R.
exists m => /= y bxy; split.
  by apply/xP/(@ball_ler _ _ m); rewrite // ler_minl lerr.
by apply/xQ/(@ball_ler _ _ m); rewrite // ler_minl lerr orbT.
Qed.

End LocallyDef.

(*compat*)
Lemma ProperFilter_ext {T} (F G : set (set T)) : (forall P, F P <-> G P) ->
  ProperFilter F -> ProperFilter G.
Proof.
move=> FG; suff <- : F = G by [].
by rewrite funeqE => P; rewrite propeqE.
Qed.


Section Locally.
Context {T : uniformType}.

Typeclasses Transparent filter_of.

Lemma locally_locally (x : T) (P : T -> Prop) :
  locally x P -> locally x (fun y => locally y P).
Proof.
move=> [dp Hp].
exists [posreal of dp / 2] => y xy.
exists [posreal of dp / 2] => z yz.
by apply Hp; rewrite (double_var dp); apply: ball_triangle xy yz.
Qed.

Lemma locally_singleton (x : T) (P : T -> Prop) : locally x P -> P x.
Proof. move=> [dp H]; by apply/H/ball_center. Qed.

Lemma locally_ball (x : T) (eps : posreal) : locally x (ball x eps).
Proof. by exists eps. Qed.

Lemma locally_not' :
  forall (x : T) (P : T -> Prop),
  not (forall eps : posreal, not (forall y, ball x eps y -> not (P y))) ->
  {d : posreal | forall y, ball x d y -> not (P y)}.
Proof.
intros x P H.
set (Q := fun z => z <= 1 /\ forall y, ball x z y -> not (P y)).
destruct (completeness Q) as [d [H1 H2]].
- exists 1.
  now intros y [Hy _].
- exists 0.
  split.
  apply Rle_0_1.
  intros y Hy Py.
  apply H.
  intros eps He.
  apply He with (2 := Py).
  apply ball_le with (2 := Hy).
  apply Rlt_le, eps.
assert (Zd : 0 < d).
  apply Rnot_le_lt.
  intros Hd.
  apply H.
  intros eps He.
  apply (Rlt_irrefl (Rmin 1 eps)).
  apply Rle_lt_trans with d.
  apply H1.
  split.
  apply Rmin_l.
  intros y By.
  apply He.
  apply ball_le with (2 := By).
  apply Rmin_r.
  apply Rle_lt_trans with (1 := Hd).
  apply Rmin_case.
  apply Rlt_0_1.
  apply cond_pos.
exists [posreal of mkposreal _ Zd / 2].
simpl.
intros y Hy HP.
apply (Rlt_not_le _ _ (Rlt_eps2_eps _ Zd)).
apply H2.
intros z Hz.
apply Rnot_lt_le.
contradict HP.
apply Hz.
apply ball_le with (2 := Hy).
now apply Rlt_le.
Qed.

Lemma locally_not (x : T) (P : T -> Prop) :
  not (forall eps : posreal, not (forall y, ball x eps y -> not (P y))) ->
  locally x (fun y => not (P y)).
Proof.
move=> H.
case: (locally_not' H) => eps He; by exists eps.
Qed.

Lemma locally_ex_not (x : T) (P : T -> Prop) :
  locally x (fun y => not (P y)) ->
  {d : posreal | forall y, ball x d y -> not (P y)}.
Proof.
move=> H.
apply locally_not'.
case: H => eps He.
by move/(_ eps).
Qed.

Lemma locally_ex_dec (x : T) (P : T -> Prop) :
  (forall x, P x \/ ~ P x) ->
  locally x P ->
  {d : posreal | forall y, ball x d y -> P y}.
Proof.
move=> P_dec H; have [|d Hd] := @locally_ex_not x (fun y => not (P y)).
  by apply: filter_imp H => y Py /(_ Py).
by exists d => y Hy; have [|/(Hd y)] := P_dec y.
Qed.

Lemma is_filter_lim_close {F} {FF : ProperFilter F} (x y : T) :
  F --> x -> F --> y -> close x y.
Proof.
intros Fx Fy eps.
specialize (Fy _ (locally_ball y [posreal of eps / 2])).
specialize (Fx _ (locally_ball x [posreal of eps / 2])).
generalize (filter_and Fx Fy) => {Fx Fy} Fxy.
rewrite (double_var eps).
destruct (filter_ex Fxy) as [z Fz].
apply ball_triangle with z.
apply Fz.
apply ball_sym, Fz.
Qed.

Lemma is_filter_lim_locally_close (x y : T) :
  x --> y -> close x y.
Proof. exact: is_filter_lim_close. Qed.

End Locally.

Definition cvg (U : Type) (T : canonical_filter U) :=
  fun (T' : Type) & canonical_filter_type T = T' =>
  fun F : set (set U) => exists l : T, F --> l.

Notation "[ 'cvg' F 'in' T ]" :=
  (@cvg _ _ T erefl [filter of F])
  (format "[ 'cvg'  F  'in'  T ]") : classical_set_scope.
Notation continuous f := (forall x, f%function @ locally x --> f%function x).

Lemma appfilter U V (f : U -> V) (F : set (set U)) : f @ F = [set P | F (f @^-1` P)].
Proof. by []. Qed.

Lemma filterlim_const {T} {U : uniformType} {F : set (set T)} {FF : Filter F} (a : U) :
  a @[_ --> F] --> a.
Proof.
move=> P [eps HP].
rewrite /filter_of /= appfilter /=.
by apply: filter_forall=> ?; apply/HP/ball_center.
Qed.

Section Cvg.

Context {U : uniformType}.

Lemma cvgE (F : set (set U)) : [cvg F in U] = (F --> lim F).
Proof. by rewrite propeqE; split => [/getPex//|]; exists (lim F). Qed.

Lemma limP (F : set (set U)) : [cvg F in U] <-> (F --> lim F).
Proof. by rewrite cvgE. Qed.

Lemma dvgP (F : set (set U)) : ~ [cvg F in U] -> lim F = point.
Proof.
by move=> dvg; rewrite [lim _]getPN // => x Fx; apply: dvg; exists x.
Qed.

CoInductive cvg_spec (F : set (set U)) : U -> Prop -> Type :=
| HasLim (l : U) of F --> l : cvg_spec F l True
| HasNoLim of ~ [cvg F in U] : cvg_spec F point False.

(* :TODO: move to boolp *)
Lemma propT (P : Prop) : P -> P = True.
Proof. by move=> p; rewrite propeqE; tauto. Qed.

(* :TODO: move to boolp *)
Lemma propF (P : Prop) : ~ P -> P = False.
Proof. by move=> p; rewrite propeqE; tauto. Qed.

Lemma cvgP (F : set (set U)) : cvg_spec F (lim F) [cvg F in U].
Proof.
have [cvg|dvg] := pselect [cvg F in U].
  by rewrite (propT cvg); apply: HasLim; rewrite -cvgE.
by rewrite (propF dvg) (dvgP _) //; apply: HasNoLim.
Qed.

Lemma close_lim (F1 F2 : set (set U)) (FF2 : ProperFilter F2):
  F1 --> F2 -> F2 --> F1 -> close (lim F1) (lim F2).
Proof.
have [l F1l _|dvgF1]:= cvgP F1.
  move=> /filter_le_trans /(_ F1l) F2l.
  apply: (@is_filter_lim_close _ F2) => //.
  by rewrite -cvgE; exists l.
have [l F2l|//]:= cvgP F2.
move=> /filter_le_trans /(_ F2l) F1l _.
by have := dvgF1 (ex_intro _ l F1l).
Qed.

End Cvg.
Arguments close_lim {U} F1 F2 {FF2} _.

Section Locally_fct.

Context {T : Type} {U : uniformType}.

Lemma filterlim_locally {F} {FF : Filter F} (y : U) :
  F --> y <-> forall eps : posreal, F [set x | ball y eps x].
Proof.
split.
- move=> Cf eps.
  apply: (Cf (fun x => ball y eps x)).
  by exists eps.
- move=> Cf P [eps He].
  apply: filter_imp (Cf eps) => t.
  exact: He.
Qed.

Lemma app_filterlim_locally {F} {FF : Filter F} (f : T -> U) y :
  f @ F --> y <-> forall eps : posreal, F [set x | ball y eps (f x)].
Proof. exact: filterlim_locally. Qed.

Lemma filterlimi_locally {F} {FF : Filter F} (f : T -> U -> Prop) y :
  f `@ F --> y <->
  forall eps : posreal, F [set x | exists z, f x z /\ ball y eps z].
Proof.
split.
- intros Cf eps.
  apply (Cf (ball y eps)).
  by exists eps.
- move=> Cf P [eps He].
  rewrite /filtermapi /filter_of /=.
  apply: filter_imp (Cf eps).
  intros t [z [Hz1 Hz2]].
  exists z.
  apply (conj Hz1).
  now apply He.
Qed.

(* :TODO: remove *)
Lemma filterlim_locally_close {F} {FF: ProperFilter F} (f : T -> U) (l l' : U) :
  f @ F --> l -> f @ F --> l' -> close l l'.
Proof. exact: is_filter_lim_close. Qed.

(* :TODO: refactor *)
Lemma filterlimi_locally_close
  {F} {FF: ProperFilter F} (f : T -> U -> Prop) (l l' : U) :
  F [set x | forall y1 y2, f x y1 -> f x y2 -> y1 = y2] ->
  f `@ F --> l ->  f `@ F --> l' -> close l l'.
Proof.
(* move=> Fmem; suff fFp : ProperFilter (f `@ F) by exact: @is_filter_lim_close. *)
(* apply: filtermapi_proper_filter. *)
(* apply: filter_imp Fmem. *)
intros Hf Hl Hl' eps.
(* have half_l := Hl (ball l ([posreal of eps / 2])) (locally_ball _ _). *)
(* have half_l' := Hl' (ball l' ([posreal of eps / 2])) (locally_ball _ _). *)
(* have := (filter_and _ _ half_l half_l'). *)
(* move=> /filter_ex [fx [fxl /ball_sym fxl']]. *)
(* by rewrite (double_var eps); eapply (ball_triangle _ fx). *)
have H := locally_ball l [posreal of eps / 2].
specialize (Hl (ball l [posreal of eps / 2]) H).
have H' := locally_ball l' [posreal of eps / 2].
specialize (Hl' (ball l' [posreal of eps / 2]) H').
unfold filtermapi in Hl, Hl'.
rewrite /filter_of /= in Hl Hl'.
generalize (filter_and Hf (filter_and Hl Hl')) => {H H' Hl Hl' Hf} H.
apply filter_ex in H.
destruct H as [x [Hf [[y [H1 H1']] [y' [H2 H2']]]]].
rewrite (double_var eps).
apply ball_triangle with y.
exact H1'.
apply ball_sym.
rewrite (Hf _ _ H1 H2).
exact H2'.
Qed.

End Locally_fct.

Lemma is_filter_lim_filtermap {T: uniformType} {U : uniformType} :
  forall (F : set (set T)) x (f : T -> U), {for x, continuous f} -> F --> x -> f @ F --> f x.
Proof.
  intros F x f Cf Fx P HP.
  apply Cf in HP.
  now apply Fx.
Qed.

(** locally' *)

Definition locally' {T : uniformType} (x : T) :=
  within (fun y => y <> x) (locally x).

Global Instance locally'_filter :
  forall {T : uniformType} (x : T), Filter (locally' x).
Proof.
intros T x.
apply within_filter.
apply locally_filter.
Qed.

Section at_point.

Context {T : uniformType}.

Definition at_point (a : T) (P : T -> Prop) : Prop := P a.

Global Instance at_point_filter (a : T) : ProperFilter (at_point a).
Proof. by constructor => //; constructor => // P Q subPQ /subPQ. Qed.

End at_point.

(** ** Open sets in uniform spaces *)

Section Open.

Context {T : uniformType}.

Definition open (D : T -> Prop) := forall x, D x -> locally x D.

Lemma locally_open (D E : T -> Prop) (OD : open D) :
  (forall x : T, D x -> E x) ->
  forall x : T, D x ->
  locally x E.
Proof.
intros H x Dx.
apply filter_imp with (1 := H).
now apply OD.
Qed.

Lemma open_ext (D E : T -> Prop) : (forall x, D x <-> E x) ->
  open D -> open E.
Proof.
intros H OD x Ex.
move: (OD x (proj2 (H x) Ex)).
apply filter_imp => y.
by apply H.
Qed.

Lemma open_and (D E : T -> Prop) : open D -> open E ->
  open (fun x => D x /\ E x).
Proof.
intros OD OE x [Dx Ex].
apply filter_and.
now apply OD.
now apply OE.
Qed.

Lemma open_or (D E : T -> Prop) : open D -> open E ->
  open (fun x => D x \/ E x).
Proof.
move=> OD OE x [Dx|Ex].
- move/filter_imp : (OD x Dx); apply; by left.
- move/filter_imp : (OE x Ex); apply; by right.
Qed.

Lemma open_true : open (fun x : T => True).
Proof. intros x _; by apply filter_true. Qed.

Lemma open_false : open (fun x : T => False).
Proof. by []. Qed.

End Open.

Lemma open_comp :
  forall {T U : uniformType} (f : T -> U) (D : U -> Prop),
  (forall x, D (f x) -> {for x, continuous f}) ->
  open D -> open (fun x : T => D (f x)).
Proof.
intros T U f D Cf OD x Dfx.
apply Cf.
exact Dfx.
now apply OD.
Qed.

(** ** Closed sets in uniform spaces *)

Section Closed.

Context {T : uniformType}.

Definition closed (D : T -> Prop) :=
  forall x, not ((locally x) (fun x : T => not (D x))) -> D x.

Lemma open_not (D : T -> Prop) : closed D -> open (fun x => not (D x)).
Proof.
intros CD x Dx.
apply locally_not.
intros H.
apply Dx, CD.
move=> [eps He].
by apply (H eps).
Qed.

Lemma closed_not (D : T -> Prop) : open D -> closed (fun x => not (D x)).
Proof.
intros OD x Lx Dx.
apply Lx.
apply: filter_imp (OD _ Dx).
intros t Dt nDt.
now apply nDt.
Qed.

Lemma closed_ext (D E : T -> Prop) : (forall x, D x <-> E x) ->
  closed D -> closed E.
Proof.
intros DE CD x Hx.
apply DE, CD.
contradict Hx.
apply: filter_imp Hx.
move => {x} x Dx Ex.
now apply Dx, DE.
Qed.

Lemma closed_and (D E : T -> Prop) : closed D -> closed E ->
  closed (fun x => D x /\ E x).
Proof.
intros CD CE x Hx; split.
- apply CD.
  contradict Hx.
  apply: filter_imp Hx.
  move => {x} x nDx [Dx _].
  now apply nDx.
- apply CE.
  contradict Hx.
  apply: filter_imp Hx.
  move => {x} x nEx [_ Ex].
  now apply nEx.
Qed.

(*
Lemma closed_or :
  forall D E : T -> Prop,
  closed D -> closed E ->
  closed (fun x => D x \/ E x).
Proof.
intros D E CD CE x Hx.
generalize (open_and _ _ CD CE).
apply open_ext.
clear ; intuition.
Qed.
*)

Lemma closed_true : closed (fun x : T => True).
Proof. by []. Qed.

Lemma closed_false : closed (fun x : T => False).
Proof.
intros x Hx.
apply: Hx.
now exists [posreal of 1].
Qed.

End Closed.

Lemma closed_comp :
  forall {T U : uniformType} (f : T -> U) (D : U -> Prop),
  continuous f ->
  closed D -> closed (fun x : T => D (f x)).
Proof.
intros T U f D Cf CD x Dfx.
apply CD.
contradict Dfx.
exact: Cf Dfx.
Qed.

Lemma closed_filterlim_loc :
  forall {T} {U : uniformType} {F} {FF : ProperFilter F} (f : T -> U) (D : U -> Prop),
  forall y, f @ F --> y ->
  F (fun x => D (f x)) ->
  closed D -> D y.
Proof.
intros T U F FF f D y Ffy Df CD.
apply CD.
intros LD.
apply: filter_not_empty.
specialize (Ffy _ LD).
unfold filtermap in Ffy.
set P := [set x | D (f x) /\ ~ D (f x)].
suff : F P by apply filter_imp => x [].
by apply: filter_and.
Qed.

Lemma closed_filterlim :
  forall {T} {U : uniformType} {F} {FF : ProperFilter F} (f : T -> U) (D : U -> Prop),
  forall y, f @ F --> y ->
  (forall x, D (f x)) ->
  closed D -> D y.
Proof.
intros T U F FF f D y Ffy Df.
apply: closed_filterlim_loc Ffy _.
now apply filter_forall.
Qed.

(** ** Complete uniform spaces *)

Definition cauchy {T : uniformType} (F : set (set T)) :=
  forall eps : posreal, exists x, F (ball x eps).

Module Complete.

Record mixin_of (T : uniformType) := Mixin {
(* TODO: replace F --> lim F by [cvg F in T] *)
  ax1 : forall (F : set (set T)), ProperFilter F -> cauchy F -> F --> lim F ;
  (* ax2 : forall (F1 F2 : set (set T)),  *)
  (*   filter_le F1 F2 -> filter_le F2 F1 -> close (lim F1) (lim F2) *)
}.

Section ClassDef.

Record class_of (T : Type) := Class {
  base : Uniform.class_of T ;
  mixin : mixin_of (Uniform.Pack base T)
}.
Local Coercion base : class_of >-> Uniform.class_of.
Local Coercion mixin : class_of >-> mixin_of.

Structure type := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).

Definition class := let: Pack _ c _ := cT return class_of cT in c.

Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 (m0 : mixin_of (@Uniform.Pack T b0 T)) :=
  fun bT b of phant_id (Uniform.class bT) b =>
  fun m of phant_id m m0 => @Pack T (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition uniformType := @Uniform.Pack cT xclass xT.

End ClassDef.

Module Exports.

Coercion base : class_of >-> Uniform.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion uniformType : type >-> Uniform.type.
Canonical uniformType.
Definition type_canonical_filter (T : type):= @CanonicalFilter T T locally.
Coercion type_canonical_filter : type >-> canonical_filter.
Canonical type_canonical_filter.
Notation completeType := type.
Notation "[ 'completeType' 'of' T 'for' cT ]" :=  (@clone T cT _ idfun)
  (at level 0, format "[ 'completeType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'completeType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'completeType'  'of'  T ]") : form_scope.
Notation CompleteType T m := (@pack T _ m _ _ idfun _ idfun).

End Exports.

End Complete.

Export Complete.Exports.

Section completeType1.

Context {T : completeType}.

Lemma complete_cauchy (F : set (set T)) (FF : ProperFilter F) :
  cauchy F -> F --> lim F.
Proof. by case: T F FF => [? [? []]]. Qed.

Lemma iota_correct_weak (P : T -> Prop) :
  (forall x y, P x -> P y -> close x y) ->
  forall x, P x -> close (iota P) x.
Proof. by move=> HP x Hx eps; apply: HP=> //; apply: getP Hx. Qed.

Lemma close_iota (P Q : T -> Prop) : (forall x, P x <-> Q x) ->
  close (iota P) (iota Q).
Proof. by move=> ?; rewrite (_ : P = Q) // funeqE => x; rewrite propeqE. Qed.

End completeType1.
Arguments complete_cauchy {T} F {FF} _.

Lemma cauchy_distance  {T : uniformType} {F} {FF : ProperFilter F} :
  (forall eps : posreal, exists x, F (ball x eps)) <->
  (forall eps : posreal, exists P, F P /\ forall u v : T, P u -> P v -> ball u eps v).
Proof.
split.
- intros H eps.
  case: (H [posreal of eps / 2]) => {H} x Hx.
  exists (ball x [posreal of eps / 2]).
  split.
  by [].
  move => u v Hu Hv.
  rewrite (double_var eps).
  apply ball_triangle with x.
  by apply ball_sym.
  exact Hv.
- intros H eps.
  case: (H eps) => {H} P [HP H].
  destruct (filter_ex HP) as [x Hx].
  exists x.
  move: (fun v => H x v Hx) => {H} H.
  apply filter_imp with (1 := H).
  by [].
Qed.

Section fct_Complete.

Context {T : choiceType} {U : completeType}.

Lemma filterlim_locally_cauchy :
  forall {F} {FF : ProperFilter F} (f : T -> U),
  (forall eps : posreal, exists P, F P /\ forall u v : T, P u -> P v -> ball (f u) eps (f v)) <->
  exists y : U, f @ F --> y.
Proof.
intros F FF f.
split.
- intros H.
  exists (lim (f @ F)).
  move=> P [eps HP] /=.
  refine (_ (complete_cauchy (f @ F) _ _)).
  + by apply => /=; exists eps.
  + clear eps P HP.
    intros eps.
    destruct (H eps) as [P [FP H']].
    destruct (filter_ex FP) as [x Hx].
    exists (f x).
    unfold filtermap.
    generalize FP.
    apply filter_imp.
    intros x' Hx'.
    now apply H'.
- intros [y Hy] eps.
  exists (fun x => ball y [posreal of eps / 2] (f x)).
  split.
  apply Hy.
  now exists [posreal of eps / 2].
- intros u v Hu Hv.
  rewrite (double_var eps).
  apply ball_triangle with y.
  apply ball_sym.
  exact Hu.
  exact Hv.
Qed.

Lemma filterlimi_locally_cauchy :
  forall {F} {FF : ProperFilter F} (f : T -> set U),
  F (fun x => (exists y, f x y) /\
    (forall y1 y2, f x y1 -> f x y2 -> y1 = y2)) ->
  ((forall eps : posreal, exists P, F P /\
   forall u v : T, P u -> P v -> forall u' v': U, f u u' -> f v v' -> ball u' eps v') <->
  exists y : U, f `@ F --> y).
Proof.
intros F FF f Hf.
assert (FF': ProperFilter (filtermapi f F)).
  apply filtermapi_proper_filter.
  exact: filter_imp Hf.
  exact FF.
split.
- intros H.
  exists (lim (f `@ F)) => P [eps HP].
  refine (_ (complete_cauchy (filtermapi f F) _ _)).
  + by apply; exists eps.
  + clear eps P HP.
    intros eps.
    case: (H eps) => {H} [P [FP H]].
    assert (FfP := filter_and Hf FP).
    destruct (filter_ex FfP) as [x [[[fx Hfx] _] Px]].
    exists fx.
    unfold filtermapi.
    apply: filter_imp FfP.
    intros x' [[[fx' Hfx'] _] Px'].
    exists fx'.
    apply (conj Hfx').
    exact: H Hfx Hfx'.
- intros [y Hy] eps.
  exists (fun x => forall fx, f x fx -> ball y [posreal of eps / 2] fx).
  split.
    have Hb := locally_ball y [posreal of eps / 2].
    assert (H := filter_and Hf (Hy _ Hb)).
    apply: filter_imp H.
    intros x [[_ H] [fx2 [Hfx2 H']]] fx Hfx.
    now rewrite <- (H fx2).
  intros u v Hu Hv fu fv Hfu Hfv.
  rewrite (double_var eps).
  apply ball_triangle with y.
  by apply/ball_sym/Hu.
  by apply Hv.
Qed.

Lemma complete_cauchy_fct :
  forall (F : ((T -> U) -> Prop) -> Prop),
  ProperFilter F -> cauchy F -> F --> lim F.
Proof.
move=> F FF Fc.
set Fr := fun (t : T) (P : U -> Prop) => F (fun g => P (g t)).
have FFr t : ProperFilter (Fr t).
  by apply: Build_ProperFilter'; apply: filter_not_empty.
have Frc t : cauchy (Fr t).
  move=> e; have [f Ffe] := Fc e; exists (f t).
  by rewrite /Fr; apply: filter_imp Ffe.
apply/limP; exists (fun t => lim (Fr t)).
apply/filterlim_locally => e.
have /cauchy_distance /(_ [posreal of e / 2]) [A [FA diamA_he]] := Fc.
apply: (filter_imp _ FA) => f Af t.
have [g [Ag limFte_gt]] :
  exists g, A g /\ ball (lim (Fr t)) [posreal of e / 2] (g t).
  apply/filter_ex/filter_and => //; apply: complete_cauchy => //.
  exact: locally_ball.
rewrite (double_var e); apply: ball_triangle limFte_gt _.
exact: diamA_he.
Qed.

Definition fct_completeType_mixin := @Complete.Mixin _ complete_cauchy_fct.
Canonical fct_completeType := CompleteType (T -> U) fct_completeType_mixin.

End fct_Complete.

(** ** Limit switching *)

Section Filterlim_switch.

Context {T1 T2 : choiceType}.

(* :TODO: Use bigenough reasonning here *)
Lemma filterlim_switch_1 {U : uniformType}
  F1 (FF1 : ProperFilter F1) F2 (FF2 : Filter F2) (f : T1 -> T2 -> U) (g : T2 -> U) (h : T1 -> U) (l : U) :
  f @ F1 --> g ->
  (forall x, f x @ F2 --> h x) ->
  h @ F1 --> l ->
  g @ F2 --> l.
Proof.
  move=> Hfg Hfh Hhl P.
  have HF1 := !! @filter_ex _ F1 _.

  apply filterlim_locally.
  move => eps.

  have {Hfg}Hfg : [filter of (F1, F2)] [set x | ball (g x.2) (eps / 2 / 2) (f x.1 x.2)].
    exists [set x | ball g (eps / 2 / 2) (f x)] setT => //=; last first.
      exact: filter_true.
      exact: (proj1 (@app_filterlim_locally _ _ F1 _ f g) _).

  have {Hhl} Hhl : [filter of (F1, F2)] [set x | ball l (eps / 2) (h x.1)].
    exists [set x | ball l (eps / 2) (h x)] setT => //=; last first.
      exact: filter_true.
    exact: (proj1 (@app_filterlim_locally _ _ F1 _ h l) _).

  have [Q R /= F1Q F2R Hfghl] := filter_and Hhl Hfg.

  move: (fun x => proj1 (@app_filterlim_locally _ _ F2 FF2 (f x) (h x)) (Hfh x) ([posreal of eps / 2 / 2])) => {Hfh} /= Hfh.
  have [x Qx] := HF1 Q F1Q.

  have {Hfh} := !! filter_and (Hfh x) F2R.
  rewrite appfilter.
  apply filter_imp => y Hy.
  rewrite (double_var eps) /=.
  apply ball_triangle with (h x).
     apply (Hfghl x y) => //.
     by apply Hy.
  rewrite (double_var (eps / 2)).
  apply ball_triangle with (f x y).
  by apply Hy.
  apply ball_sym, Hfghl.
  by [].
  by apply Hy.
Qed.

(* :TODO: Use bigenough reasonning here *)
Lemma filterlim_switch_2 {U : completeType}
  F1 (FF1 : ProperFilter F1) F2 (FF2 : ProperFilter F2) (f : T1 -> T2 -> U) (g : T2 -> U) (h : T1 -> U) :
  f @ F1 --> g ->
  (forall x, f x @ F2 --> h x) ->
  [cvg h @ F1 in U].

Proof.
  move => Hfg Hfh.
  case : (proj1 (filterlim_locally_cauchy h)).
  move => eps.
  generalize (proj2 (filterlim_locally_cauchy f)) => Hf.
  assert (exists y : T2 -> U, f @ F1 --> y).
    exists g => P Hp.
    apply Hfg.
    case: Hp => d Hp.
    exists d => y Hy.
    apply: Hp.
    by apply Hy.

  move: H => {Hfg} Hfg.
  move: (Hf Hfg [posreal of eps / 2]) => {Hf Hfg} /= Hf.

  have HF2 := !! @filter_ex _ F2 _.
  generalize (fun x => proj1 (app_filterlim_locally (f x) (h x)) (Hfh x) ([posreal of eps / 2 / 2]))
    => {Hfh} Hfh.

  case: Hf => P [Hp Hf].
  exists P ; split.
  by [].
  move => u v Hu Hv.
  move: (Hfh u) => /= Hu'.
  move: (Hfh v) => /= Hv'.
  move: (!! (@filter_and _ F2 _ _ _ Hu' Hv')) => {Hu' Hv' Hfh} Hfh.
  case: (HF2 _ Hfh) => {Hfh} y Hy.
  replace (pos eps) with (eps / 2 / 2 + (eps / 2 + eps / 2 / 2)) by field.
  apply ball_triangle with (f u y).
  by apply Hy.
  apply ball_triangle with (f v y).
  by apply Hf.
    apply ball_sym.
    by apply Hy.
  move => l Hl.
  by exists l.
Qed.

(* Alternative version *)
(* Lemma filterlim_switch {U : completeType} *)
(*   F1 (FF1 : ProperFilter F1) F2 (FF2 : ProperFilter F2) (f : T1 -> T2 -> U) (g : T2 -> U) (h : T1 -> U) : *)
(*   [cvg f @ F1 in T2 -> U] -> (forall x, [cvg f x @ F2 in U]) -> *)
(*   [/\ [cvg [lim f @ F1] @ F2 in U], [cvg (fun x => [lim f x @ F2]) @ F1 in U] *)
(*   & [lim [lim f @ F1] @ F2] = [lim (fun x => [lim f x @ F2]) @ F1]]. *)
Lemma filterlim_switch {U : completeType}
  F1 (FF1 : ProperFilter F1) F2 (FF2 : ProperFilter F2) (f : T1 -> T2 -> U) (g : T2 -> U) (h : T1 -> U) :
  f @ F1 --> g ->
  (forall x, f x @ F2 --> h x) ->
  exists l : U, h @ F1 --> l /\ g @ F2 --> l.
Proof.
  move => Hfg Hfh.
  destruct (filterlim_switch_2 FF1 FF2 Hfg Hfh) as [l Hhl].
  exists l ; split.
  exact Hhl.
  case: FF2 => HF2 FF2.
  now apply (@filterlim_switch_1 _ F1 FF1 F2 FF2 f g h l).
Qed.

End Filterlim_switch.

(* TODO: fix this later by instanciating a choicetype on sig *)
(* Lemma filterlim_switch_dom {T1 T2 : choiceType} {U : completeType} *)
(*   F1 (FF1 : ProperFilter F1) F2 (FF2 : Filter F2) *)
(*   (dom : T2 -> Prop) (HF2 : forall P, F2 P -> exists x, dom x /\ P x) *)
(*   (f : T1 -> T2 -> U) (g : T2 -> U) (h : T1 -> U) : *)
(*   (fun x (y : {z : T2 | dom z}) => f x (proj1_sig y)) @ F1 *)
(*      --> (fun y : {z : T2 | dom z} => g (proj1_sig y)) -> *)
(*   (forall x, (f x) @ (within dom F2) --> h x) -> *)
(*   exists l : U, h @ F1 --> l /\ g @ within dom F2 --> l. *)
(* Proof. *)
(* set (T2' := { y : T2 | dom y }). *)
(* set (f' := fun x (y : T2') => f x (proj1_sig y)). *)
(* set (F2' := fun P : T2' -> Prop => F2 (fun x => forall (H:dom x), P (exist _ x H))). *)
(* set (g' := fun y : T2' => g (proj1_sig y)). *)
(* intros Hfg Hfh. *)
(* refine (filterlim_switch F1 FF1 F2' _ f' g' h _ _). *)
(* now apply subset_filter_proper. *)
(* intros H P. *)
(* now apply Hfg. *)
(* intros x P HP. *)
(* now apply Hfh. *)
(* Qed. *)

(** ** Modules with a norm *)

Module AbsRing.

Close Scope R_scope.

Record mixin_of (D : ringType) := Mixin {
  abs : D -> R;
  ax1 : abs 0 = 0 ;
  ax2 : abs (- 1) = 1 ;
  ax3 : forall x y : D, abs (x + y) <= abs x + abs y ;
  ax4 : forall x y : D, abs (x * y) <= abs x * abs y ;
  ax5 : forall x : D, abs x = 0 -> x = 0
}.

Section ClassDef.

Record class_of (K : Type) := Class {
  base : Num.NumDomain.class_of K ;
  mixin : mixin_of (Num.NumDomain.Pack base K)
}.
Local Coercion base : class_of >-> Num.NumDomain.class_of.
Local Coercion mixin : class_of >-> mixin_of.

Structure type := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ := cT return class_of cT in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).
Definition clone c of phant_id class c := @Pack T c T.
Definition pack b0 (m0 : mixin_of (@Num.NumDomain.Pack T b0 T)) :=
  fun bT b & phant_id (Num.NumDomain.class bT) b =>
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

End ClassDef.

Module Exports.

Coercion base : class_of >-> Num.NumDomain.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
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
Notation AbsRingMixin := Mixin.
Notation AbsRingType T m := (@pack T _ m _ _ id _ id).
Notation "[ 'absRingType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'absRingType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'absRingType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'absRingType'  'of'  T ]") : form_scope.
Notation absRingType := type.

End Exports.

End AbsRing.

Export AbsRing.Exports.

Delimit Scope R_scope with coqR.
Delimit Scope real_scope with real.
Local Open Scope ring_scope.
Local Open Scope real_scope.

Context {K : absRingType}.

Definition abs {K : absRingType} : K -> R := @AbsRing.abs _ (AbsRing.class K).
Notation "`| x |" := (abs x%R) : R_scope.
Notation "`| x |" := (abs x%R) : real_scope.

Section AbsRing1.

Context {K : absRingType}.
Implicit Types x : K.

Lemma absr0 : `|0 : K| = 0. Proof. exact: AbsRing.ax1. Qed.

Lemma absrN1: `|- 1 : K| = 1.
Proof. exact: AbsRing.ax2. Qed.

Lemma ler_abs_add (x y : K) :  `|x + y| <= `|x|%real + `|y|%real.
Proof. exact: AbsRing.ax3. Qed.

Lemma absrM (x y : K) : `|x * y| <= `|x|%real * `|y|%real.
Proof. exact: AbsRing.ax4. Qed.

Lemma absr0_eq0 (x : K) : `|x| = 0 -> x = 0.
Proof. exact: AbsRing.ax5. Qed.

Lemma absrN x : `|- x| = `|x|.
Proof.
gen have le_absN1 : x / `|- x| <= `|x|.
  by rewrite -mulN1r (ler_trans (absrM _ _)) //= absrN1 mul1r.
by apply/eqP; rewrite eqr_le le_absN1 /= -{1}[x]opprK le_absN1.
Qed.

Lemma absrB (x y : K) : `|x - y| = `|y - x|.
Proof. by rewrite -absrN opprB. Qed.

Lemma absr1 : `|1 : K| = 1. Proof. by rewrite -absrN absrN1. Qed.

Lemma absr_ge0 x : 0 <= `|x|.
Proof.
rewrite -(@pmulr_rge0 _ 2%:R) // mulr2n mulrDl !mul1r.
by rewrite -{2}absrN (ler_trans _ (ler_abs_add _ _)) // subrr absr0.
Qed.

Lemma absrX x n : `|x ^+ n| <= `|x|%real ^+ n.
Proof.
elim: n => [|n IH]; first  by rewrite !expr0 absr1.
by rewrite !exprS (ler_trans (absrM _ _)) // ler_pmul // absr_ge0.
Qed.

End AbsRing1.

Section AbsRing_UniformSpace.

Context (K : absRingType).

Definition AbsRing_ball (x : K) (eps : R) (y : K) := `|x - y| < eps.

Lemma AbsRing_ball_center (x : K) (e : posreal) : AbsRing_ball x e x.
Proof. by rewrite /AbsRing_ball subrr absr0. Qed.

Lemma AbsRing_ball_sym (x y : K) (e : R) :
  AbsRing_ball x e y -> AbsRing_ball y e x.
Proof. by rewrite /AbsRing_ball absrB. Qed.

(* :TODO: to math-comp *)
Lemma subr_trans (M : zmodType) (z x y : M) : x - y = (x - z) + (z - y).
Proof. by rewrite addrA addrNK. Qed.

Lemma AbsRing_ball_triangle (x y z : K) (e1 e2 : R) :
  AbsRing_ball x e1 y -> AbsRing_ball y e2 z -> AbsRing_ball x (e1 + e2) z.
Proof.
rewrite /AbsRing_ball => xy yz.
by rewrite (subr_trans y) (ler_lt_trans (ler_abs_add _ _)) ?ltr_add.
Qed.

Definition AbsRingUniformMixin :=
  UniformMixin 0 AbsRing_ball_center AbsRing_ball_sym AbsRing_ball_triangle.

(* :TODO: DANGEROUS ! Must change this to include uniform type inside absring *)
Canonical absRing_UniformType := UniformType K AbsRingUniformMixin.
Canonical AbsRingcanonical_filter := @CanonicalFilter K K locally.

End AbsRing_UniformSpace.

(* We should have compatilibity modules for every lemma in Hierarchy
that we deleted (and replaced by mathcomp's ones) so that the rest of
Coquelicot compiles just with a import of The compatibility modules *)
Module AbsRingCompat.
Notation AbsRing := absRingType.
Module AbsRing.
  Notation Pack := AbsRing.
End AbsRing.
Context {K : absRingType}.
Definition abs_zero  := @absr0 K. (*compat*)
Definition abs_opp_one := @absrN1 K. (*compat*)
Definition abs_triangle := @ler_abs_add K. (*compat*)
Definition abs_mult := @absrM K. (*compat*)
Definition abs_eq_zero := @absr0_eq0 K. (*compat*)
Definition abs_opp := @absrN K. (*compat*)
Definition abs_minus := @absrB K. (*compat*)
Definition abs_one := @absr1 K. (*compat*)
Definition abs_pow_n := @absrX K. (*compat*)
End AbsRingCompat.
Import AbsRingCompat.

Reserved Notation  "`|[ x ]|" (at level 0, x at level 99, format "`|[ x ]|").

Module NormedModule.

Close Scope R_scope.

Record mixin_of (K : absRingType) (V : lmodType K) (m : Uniform.mixin_of V) := Mixin {
  norm : V -> R ;
  norm_factor : R ;
  ax1 : forall (x y : V), norm (x + y) <= norm x + norm y ;
  ax2 : forall (l : K) (x : V), norm (l *: x) <= abs l * norm x;
  ax3 : forall (x y : V) (eps : posreal), norm (x - y) < eps -> Uniform.ball m x eps y ;
  ax4 : forall (x y : V) (eps : posreal), Uniform.ball m x eps y ->
    norm (x - y) < norm_factor * eps ;
  ax5 : forall x : V, norm x = 0 -> x = 0
}.

Section ClassDef.

Variable K : absRingType.

Record class_of (T : Type) := Class {
  base : GRing.Lmodule.class_of K T ;
  uniform_mixin : Uniform.mixin_of T ;
  mixin : @mixin_of _ (@GRing.Lmodule.Pack K (Phant K) T base T) uniform_mixin
}.
Local Coercion base : class_of >-> GRing.Lmodule.class_of.
Definition base2 T (c : class_of T) :=
  Uniform.Class (@base T c) (@uniform_mixin T c).
Local Coercion base2 : class_of >-> Uniform.class_of.
Local Coercion mixin : class_of >-> mixin_of.

Structure type (phK : phant K) :=
  Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.

Variables (phK : phant K) (T : Type) (cT : type phK).

Definition class := let: Pack _ c _ := cT return class_of cT in c.
Definition clone c of phant_id class c := @Pack phK T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 um0 (m0 : @mixin_of _ (@GRing.Lmodule.Pack K (Phant K) T b0 T) um0) :=
  fun bT b & phant_id (@GRing.Lalgebra.class K phK bT) b =>
  fun ubT (ub : Uniform.class_of _) & phant_id (@Uniform.class ubT) ub =>
  fun   m & phant_id m0 m => Pack phK (@Class T b ub m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @GRing.Zmodule.Pack cT xclass xT.
Definition lmodType := @GRing.Lmodule.Pack K phK cT xclass xT.
Definition uniformType := @Uniform.Pack cT xclass xT.
Definition join_zmodType := @GRing.Zmodule.Pack uniformType xclass xT.
Definition join_lmodType := @GRing.Lmodule.Pack K phK uniformType xclass xT.
End ClassDef.

Module Exports.

Coercion base : class_of >-> GRing.Lmodule.class_of.
Coercion base2 : class_of >-> Uniform.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion lmodType : type >-> GRing.Lmodule.type.
Canonical lmodType.
Coercion uniformType : type >-> Uniform.type.
Canonical uniformType.
Canonical join_zmodType.
Canonical join_lmodType.
Definition type_canonical_filter
   (K : absRingType) (phK : phant K) (T : type phK) :=
  @CanonicalFilter T T locally.
Coercion type_canonical_filter : type >-> canonical_filter.
Canonical type_canonical_filter.

Notation normedModType K := (type (Phant K)).
Notation NormedModType K T m := (@pack _ (Phant K) T _ _ m _ _ id _ _ id _ id).
Notation NormedModMixin := Mixin.
Notation "[ 'normedModType' K 'of' T 'for' cT ]" := (@clone _ (Phant K) T cT _ idfun)
  (at level 0, format "[ 'normedModType'  K  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'normedModType' K 'of' T ]" := (@clone _ (Phant K) T _ _ id)
  (at level 0, format "[ 'normedModType'  K  'of'  T ]") : form_scope.

End Exports.

End NormedModule.

Export NormedModule.Exports.

Program Definition R_AbsRingMixin :=
 @AbsRing.Mixin _ normr (normr0 _) (normrN1 _) (@ler_norm_add _) _ (@normr0_eq0 _).
Next Obligation. by rewrite normrM. Qed.
Canonical R_absRingType := AbsRingType R R_AbsRingMixin.

Definition R_UniformSpace_mixin := @AbsRingUniformMixin R_absRingType.
Canonical R_UniformSpace := UniformType R R_UniformSpace_mixin.
Canonical R_canonical_filter := @CanonicalFilter R R locally.


Definition norm {K : absRingType} {V : normedModType K} : V -> R :=
  NormedModule.norm (NormedModule.class _).
Definition norm_factor {K : absRingType} (V : normedModType K) : R :=
 @NormedModule.norm_factor _ _ _ (@NormedModule.class _ _ V).
Notation "`|[ x ]|" := (norm x) : ring_scope.

Section NormedModule1.
Context {K : absRingType} {V : normedModType K}.
Implicit Types (l : K) (x y : V) (eps : posreal).

Close Scope R_scope.

Lemma ler_normm_add x y : `|[x + y]| <= `|[x]| + `|[y]|.
Proof. exact: NormedModule.ax1. Qed.
Definition norm_triangle := ler_normm_add. (*compat*)

Lemma ler_normmZ l x : `|[l *: x]| <= `|l|%real * `|[x]|.
Proof. exact: NormedModule.ax2. Qed.
Definition norm_scal := ler_normmZ. (*compat*)

Definition ball_norm x (eps : R) y := `|[x - y]| < eps.
Arguments ball_norm x eps%R y /.

Lemma sub_norm_ball_pos (x : V) (eps : posreal) : ball_norm x eps `<=` ball x eps.
Proof. move=> y; exact: NormedModule.ax3. Qed.
Definition norm_compat1 := sub_norm_ball_pos.

Lemma sub_ball_norm_pos (x : V) (eps : posreal) : ball x eps `<=` ball_norm x (norm_factor V * eps).
Proof. move=> y; exact: NormedModule.ax4. Qed.
Definition norm_compat2 := sub_ball_norm_pos.

Lemma normm0_eq0 x : `|[x]| = 0 -> x = 0.
Proof. exact: NormedModule.ax5. Qed.
Definition norm_eq_zero := normm0_eq0.

Lemma normmN x : `|[- x]| = `|[x]|.
Proof.
gen have le_absN1 : x / `|[- x]| <= `|[x]|.
  by rewrite -scaleN1r (ler_trans (ler_normmZ _ _)) //= absrN1 mul1r.
by apply/eqP; rewrite eqr_le le_absN1 /= -{1}[x]opprK le_absN1.
Qed.

Lemma normmB x y : `|[x - y]| = `|[y - x]|.
Proof. by rewrite -normmN opprB. Qed.

Lemma normm0 : `|[0 : V]| = 0.
Proof.
apply/eqP; rewrite eqr_le; apply/andP; split.
  by rewrite -{1}(scale0r 0) (ler_trans (ler_normmZ _ _)) ?absr0 ?mul0r.
by rewrite -(ler_add2r `|[0 : V]|) add0r -{1}[0 : V]add0r ler_normm_add.
Qed.
Definition norm_zero := normm0.
Hint Resolve normm0.

Lemma normm_eq0 x : (`|[x]| == 0) = (x == 0).
Proof. by apply/eqP/eqP=> [/normm0_eq0|->//]. Qed.

Lemma normm_ge0 x : 0 <= `|[x]|.
Proof.
rewrite -(@pmulr_rge0 _ 2%:R) // mulr2n mulrDl !mul1r.
by rewrite -{2}normmN (ler_trans _ (ler_normm_add _ _)) // subrr normm0.
Qed.

Lemma normm_gt0 x : (0 < `|[x]|) = (x != 0).
Proof. by rewrite ltr_def normm_eq0 normm_ge0 andbT. Qed.

Lemma normm_lt0 x : (`|[x]| < 0) = false.
Proof. by rewrite ltrNge normm_ge0. Qed.

Lemma norm_factor_gt_0 : 0 < norm_factor V.
Proof.
have /= := @sub_ball_norm_pos 0 [posreal of (1 : R)].
by move=> /(_ 0 (ball_center _ _)) /=; rewrite subrr normm0 mulr1.
Qed.
Canonical norm_factor_posreal := PosReal norm_factor_gt_0.

Lemma absRE (x : R) : `|x|%real = `|x|%R.
Proof. by []. Qed.

Lemma ler_distm_dist x y : `| `|[x]| - `|[y]| | <= `|[x - y]|.
Proof.
wlog gt_xy : x y / `|[x]| >= `|[y]| => [hw|].
  by have [/hw//|/ltrW/hw] := lerP `|[y]| `|[x]|; rewrite absRE distrC normmB.
rewrite absRE ger0_norm ?subr_ge0 // ler_subl_addr.
by rewrite -{1}[x](addrNK y) ler_normm_add.
Qed.
Definition norm_triangle_inv := ler_distm_dist.

Lemma sub_norm_ball (x : V) (eps : R) : ball_norm x eps `<=` ball x eps.
Proof.
move=> y /=; have [/ltr_le_trans lt /lt|eps_gt0] := ler0P eps.
  by rewrite normm_lt0.
by apply: (@sub_norm_ball_pos _ (PosReal eps_gt0)).
Qed.

Lemma sub_ball_norm_rev (x : V) (eps : posreal) :
  ball x ((norm_factor V)^-1 * eps) `<=` ball_norm x eps.
Proof. by move=> y /sub_ball_norm_pos /=; rewrite mulVKf. Qed.

Lemma closeE x y : close x y = (x = y).
Proof.
rewrite propeqE; split => [cl_xy|->//]; have [//|neq_xy] := eqVneq x y.
have dxy_gt0 : `|[x - y]| > 0 by rewrite normm_gt0 subr_eq0.
have dxy_ge0 := ltrW dxy_gt0.
have /sub_ball_norm_pos/= := cl_xy
  [posreal of ((norm_factor V)^-1 * (((PosReal dxy_gt0) : R) / 2%:R))%R].
rewrite mulVKf // -subr_lt0 ler_gtF //.
rewrite -[X in X - _]mulr1 -mulrBr mulr_ge0 //.
by rewrite subr_ge0 -(@ler_pmul2r _ 2%:R) // mulVf // mul1r ler1n.
Qed.

Definition locally_norm (x : V) (P : V -> Prop) :=
  exists eps : posreal, forall y, ball_norm x eps y -> P y.

Lemma locally_le_locally_norm x : filter_le (locally x) (locally_norm x).
Proof. by move=> P [e H]; eexists=> y Py; apply/H/sub_ball_norm_rev/Py. Qed.

Lemma locally_norm_le_locally x : filter_le (locally_norm x) (locally x).
Proof. by move=> P [e Pxe]; exists e => y /sub_norm_ball /Pxe. Qed.

(* NB: this lemmas was not here before *)
Lemma locally_locally_norm : locally_norm = locally.
Proof.
rewrite funeqE => x; rewrite funeqE => s; rewrite propeqE; split;
by [apply locally_le_locally_norm | apply locally_norm_le_locally].
Qed.

Lemma locally_norm_ball_norm x (e : posreal) : locally_norm x (ball_norm x e).
Proof. by exists e. Qed.

Lemma locally_norm_ball x (eps : posreal) : locally_norm x (ball x eps).
Proof. rewrite locally_locally_norm; by apply: locally_ball. Qed.

Lemma locally_ball_norm (x : V) (eps : posreal) : locally x (ball_norm x eps).
Proof. rewrite -locally_locally_norm; apply locally_norm_ball_norm. Qed.

Lemma ball_norm_triangle (x y z : V) (e1 e2 : R) :
  ball_norm x e1 y -> ball_norm y e2 z -> ball_norm x (e1 + e2) z.
Proof.
rewrite /ball_norm => H1 H2; rewrite (subr_trans y).
by rewrite (ler_lt_trans (ler_normm_add _ _)) ?ltr_add.
Qed.

Lemma ball_norm_center (x : V) (e : posreal) : ball_norm x e x.
Proof. apply/RltbP; rewrite subrr normm0; exact: cond_pos. Qed.

Lemma ball_norm_dec x y (e : R) : {ball_norm x e y} + {~ ball_norm x e y}.
Proof. exact: pselect. Qed.

Lemma ball_norm_sym x y (e : R) : ball_norm x e y -> ball_norm y e x.
Proof. by rewrite /ball_norm -opprB normmN. Qed.

Lemma ball_norm_le x (e1 e2 : R) :
  e1 <= e2 -> ball_norm x e1 `<=` ball_norm x e2.
Proof. by move=> e1e2 y /ltr_le_trans; apply. Qed.

Lemma norm_close x y : close x y = (forall eps : posreal, ball_norm x eps y).
Proof.
rewrite propeqE; split=> [cxy eps|cxy eps]; last exact: sub_norm_ball.
exact/sub_ball_norm_rev/cxy.
Qed.

Lemma ball_norm_eq x y : (forall eps : posreal, ball_norm x eps y) -> x = y.
Proof. by rewrite -norm_close closeE. Qed.

Lemma is_filter_lim_unique {F} {FF : ProperFilter F} (x y : V) :
  F --> x -> F --> y -> x = y.
Proof. by move=> Fx Fy; rewrite -closeE; apply: is_filter_lim_close. Qed.

Lemma is_filter_lim_locally_unique (x y : V) : x --> y -> x = y.
Proof. move=> H; rewrite -closeE; by apply/is_filter_lim_locally_close. Qed.

End NormedModule1.

Section NormedModule2.

Context {T : Type} {K : absRingType} {V : normedModType K}.

Lemma filterlim_locally_unique {F} {FF : ProperFilter F} (f : T -> V) (x y : V) :
  f @ F --> x -> f @ F --> y -> x = y.
Proof. exact: is_filter_lim_unique. Qed.

Lemma filterlimi_locally_unique {F} {FF : ProperFilter F} (f : T -> V -> Prop) (x y : V) :
  F (fun x => forall y1 y2, f x y1 -> f x y2 -> y1 = y2) ->
  f `@ F --> x -> f `@ F --> y -> x = y.
Proof.
move=> ffun fx fy; rewrite -closeE.
exact: (@filterlimi_locally_close _ _ _ _ f).
Qed.

End NormedModule2.

(** Rings with absolute values are normed modules *)

Section AbsRing_NormedModule.

Variable (K : absRingType).

(*Canonical AbsRing_NormedModuleAux :=
  NormedModuleAux.Pack K K (NormedModuleAux.Class _ _ (ModuleSpace.class _ (AbsRing_ModuleSpace K)) (Uniform.class (AbsRing_uniformType K))) K.*)

Lemma tmp (x y : [lmodType K of K^o]) (eps : posreal) :
 `|x - y| < eps -> Uniform.ball (Uniform.class (absRing_UniformType K)) x eps y.
Proof.
move=> H.
(* TODO: should not call ax3 *)
move: (@NormedModule.ax3 K [lmodType K of K^o] (Uniform.class (absRing_UniformType K))).
apply.
Admitted.

Lemma tmp2 (x y : [lmodType K of K^o]) (eps : posreal) :
 Uniform.ball (Uniform.class (absRing_UniformType K)) x eps y -> `|x - y| < 1 * pos eps.
Proof.
move=> H.
Admitted.

Definition AbsRing_NormedModule_mixin :=
  @NormedModule.Mixin K [lmodType K of K^o] (Uniform.class _) abs 1 ler_abs_add absrM tmp tmp2 absr0_eq0.

Canonical AbsRing_NormedModule :=
  NormedModule.Pack (*K*) _ (NormedModule.Class (*_ _ _*) AbsRing_NormedModule_mixin) K.

End AbsRing_NormedModule.

(* COMPILES UNTIL HERE *)

(*
(** Rings with absolute values are normed modules *)

Section AbsRing_NormedModule.

Variable (K : AbsRing).

Canonical AbsRing_NormedModuleAux :=
  NormedModuleAux.Pack K K (NormedModuleAux.Class _ _ (ModuleSpace.class _ (AbsRing_ModuleSpace K)) (Uniform.class (AbsRing_uniformType K))) K.

Lemma AbsRing_norm_compat2 :
  forall (x y : AbsRing_NormedModuleAux) (eps : posreal),
  ball x eps y -> abs (minus y x) < 1 * eps.
Proof.
  intros x y eps H.
  now rewrite Rmult_1_l.
Qed.

Definition AbsRing_NormedModule_mixin :=
  NormedModule.Mixin K _ abs 1 abs_triangle abs_mult (fun x y e H => H) AbsRing_norm_compat2 abs_eq_zero.

Canonical AbsRing_NormedModule :=
  NormedModule.Pack K _ (NormedModule.Class _ _ _ AbsRing_NormedModule_mixin) K.

End AbsRing_NormedModule.

(* Quick fix for non inferred instances *)
(* This does not fix everything, see below *)
Instance NormedModule_locally_filter (K : AbsRing) (V : NormedModule K)
  (p : V) :
  @ProperFilter (NormedModule.sort K V)
  (@locally (NormedModule.uniformType _ _)  p).
Proof. exact: locally_filter. Qed.

(* Lemma bla (K : AbsRing) (x : K) : *)
(*   @ProperFilter (NormedModuleAux.sort K (AbsRing_NormedModuleAux K)) *)
(*   (@locally (AbsRing_uniformType K) x). *)
(* Proof. *)
(* Fail typeclasses eauto. *)
(* exact: locally_filter. *)
(* Abort. *)

(** Normed vector spaces have some continuous functions *)

Section NVS_continuity.

Context {K : AbsRing} {V : NormedModule K}.

Lemma filterlim_plus :
  forall x y : V,
  (fun z : V * V => plus (fst z) (snd z)) @ (x, y) --> (plus x y).
Proof.
intros x y.
apply (filterlim_filter_le_1 (F := filter_prod (locally_norm x) (locally_norm y))).
  intros P [Q R LQ LR H].
  exists Q R.
  now apply locally_le_locally_norm.
  now apply locally_le_locally_norm.
  exact H.
apply (filterlim_filter_le_2 (G := locally_norm (plus x y))).
  apply locally_norm_le_locally.
intros P [eps HP].
exists (ball_norm x [posreal of eps / 2]) (ball_norm y [posreal of eps / 2]).
by apply locally_norm_ball_norm.
by apply locally_norm_ball_norm.
intros u v Hu Hv.
apply HP.
rewrite /ball_norm /= (double_var eps).
apply Rle_lt_trans with (2 := Rplus_lt_compat _ _ _ _ Hu Hv).
apply Rle_trans with (2 := norm_triangle _ _).
apply Req_le, f_equal.
rewrite /minus /= opp_plus -2!plus_assoc.
apply f_equal.
rewrite 2!plus_assoc.
apply f_equal2.
by apply plus_comm.
by [].
Qed.

Lemma filterlim_scal (k : K) (x : V) :
  (fun z => scal (fst z) (snd z)) @ (k, x) --> (scal k x).
Proof.
apply/filterlim_locally => /= eps.
eapply filter_imp.
move => /= u Hu.
rewrite (double_var eps).
apply ball_triangle with (scal (fst u) x).
apply norm_compat1.
rewrite -scal_minus_distr_r.
eapply Rle_lt_trans.
apply norm_scal.
eapply Rle_lt_trans.
apply Rmult_le_compat_l.
by apply abs_ge_0.
apply Rlt_le, Rlt_plus_1.
apply <- Rlt_div_r.
2: apply Rle_lt_0_plus_1, norm_ge_0.
by eapply (proj1 Hu).
apply norm_compat1.
rewrite -scal_minus_distr_l.
eapply Rle_lt_trans.
apply norm_scal.
eapply Rle_lt_trans.
apply Rmult_le_compat_r.
by apply norm_ge_0.
replace (fst u) with (plus k (minus (fst u) k)).
eapply Rle_trans.
apply abs_triangle.
apply Rplus_le_compat_l.
apply Rlt_le.
instantiate (1 := 1).
eapply (proj1 (proj2 Hu)).
by rewrite plus_comm -plus_assoc plus_opp_l plus_zero_r.
rewrite Rmult_comm.
apply <- Rlt_div_r.
2: apply Rle_lt_0_plus_1, abs_ge_0.
by apply (proj2 (proj2 Hu)).

repeat apply filter_and.
assert (Hd : 0 < eps / 2 / (norm x + 1)).
  apply: Rdiv_lt_0_compat => //.
  apply Rle_lt_0_plus_1, norm_ge_0.
eexists.
apply (locally_ball_norm (V := AbsRing_NormedModule K) _ (mkposreal _ Hd)).
apply: filter_true.
by [].

eexists.
apply (locally_ball_norm (V := AbsRing_NormedModule K) _ [posreal of 1]).
apply: filter_true.
by [].

assert (Hd : 0 < eps / 2 / (abs k + 1)).
  apply: Rdiv_lt_0_compat => //.
  apply Rle_lt_0_plus_1, abs_ge_0.
eexists.
apply: filter_true.
apply (locally_ball_norm _ (mkposreal _ Hd)).
by [].
Qed.

Lemma filterlim_scal_r (k : K) (x : V) :
  (fun z : V => scal k z) @ x --> (scal k x).
Proof.
  eapply filterlim_comp_2.
  by apply filterlim_const.
  by apply filterlim_id.
  by apply filterlim_scal.
Qed.
Lemma filterlim_scal_l (k : K) (x : V) :
  (fun z => scal z x) @ k --> (scal k x).
Proof.
  eapply filterlim_comp_2.
  by apply filterlim_id.
  by apply filterlim_const.
  by apply filterlim_scal.
Qed.

Lemma filterlim_opp (x : V) : opp @ x --> (opp x).
Proof.
rewrite -scal_opp_one.
apply filterlim_ext with (2 := filterlim_scal_r _ _).
apply: scal_opp_one.
Qed.

End NVS_continuity.

Lemma filterlim_mult {K : AbsRing} (x y : K) :
  (fun z => mult (fst z) (snd z)) @ (x , y) --> (mult x y).
Proof.
  by apply @filterlim_scal.
Qed.

Lemma filterlim_locally_ball_norm {K : AbsRing} {T} {U : NormedModule K}
  {F : set (set T)} {FF : Filter F} (f : T -> U) (y : U) :
  f @ F --> y <-> forall eps : posreal, F (fun x => ball_norm y eps (f x)).
Proof.
split.
- intros Cf eps.
  apply (Cf (fun x => ball_norm y eps x)).
  apply locally_le_locally_norm.
  apply locally_norm_ball_norm.
- intros Cf.
  apply (filterlim_filter_le_2 _ (locally_norm_le_locally y)).
  intros P [eps He].
  apply: filter_imp (Cf eps).
  intros t.
  apply He.
Qed.

(** ** Complete Normed Modules *)

Module CompleteNormedModule.

Section ClassDef.

Variable K : AbsRing.

Record class_of (T : Type) := Class {
  base : NormedModule.class_of K T ;
  mixin : Complete.mixin_of (Uniform.Pack T base T)
}.
Local Coercion base : class_of >-> NormedModule.class_of.
Definition base2 T (cT : class_of T) : Complete.class_of T :=
  Complete.Class _ (base T cT) (mixin T cT).
Local Coercion base2 : class_of >-> Complete.class_of.

Structure type := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.

Variable cT : type.

Definition class := let: Pack _ c _ := cT return class_of cT in c.

Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition AbelianGroup := AbelianGroup.Pack cT xclass xT.
Definition ModuleSpace := ModuleSpace.Pack _ cT xclass xT.
Definition NormedModuleAux := NormedModuleAux.Pack _ cT xclass xT.
Definition NormedModule := NormedModule.Pack _ cT xclass xT.
Definition uniformType := Uniform.Pack cT xclass xT.
Definition completeType := Complete.Pack cT xclass xT.

End ClassDef.

Module Exports.

Coercion base : class_of >-> NormedModule.class_of.
Coercion mixin : class_of >-> Complete.mixin_of.
Coercion base2 : class_of >-> Complete.class_of.
Coercion sort : type >-> Sortclass.
Coercion AbelianGroup : type >-> AbelianGroup.type.
Canonical AbelianGroup.
Coercion ModuleSpace : type >-> ModuleSpace.type.
Canonical ModuleSpace.
Coercion NormedModuleAux : type >-> NormedModuleAux.type.
Canonical NormedModuleAux.
Coercion NormedModule : type >-> NormedModule.type.
Canonical NormedModule.
Coercion uniformType : type >-> Uniform.type.
Canonical Uniform.
Coercion completeType : type >-> Complete.type.
Canonical Complete.
Definition type_canonical_filter R (T : type R):= CanonicalFilter T T locally.
Coercion type_canonical_filter : type >-> canonical_filter.
Canonical type_canonical_filter.
Notation CompleteNormedModule := type.

End Exports.

End CompleteNormedModule.

Export CompleteNormedModule.Exports.

Section CompleteNormedModule1.

Context {K : AbsRing} {V : CompleteNormedModule K}.

Lemma iota_unique :
  forall (P : V -> Prop) (x : V),
  (forall y, P y -> y = x) ->
  P x ->
  iota P = x.
Proof.
intros P x HP Px.
apply eq_close.
intros eps.
apply: iota_correct_weak Px eps.
intros x' y Px' Py eps.
rewrite (HP _ Py) -(HP _ Px').
apply ball_center.
Qed.

Lemma iota_correct :
  forall P : V -> Prop,
  (exists! x : V, P x) ->
  P (iota P).
Proof.
intros P [x [Px HP]].
rewrite (iota_unique _ x) ; try exact Px.
intros y Py.
now apply sym_eq, HP.
Qed.

Lemma iota_is_filter_lim {F} {FF : ProperFilter F} (l : V) :
  F --> l -> iota [set l | F --> l] = l.
Proof.
intros Hl.
apply: iota_unique (Hl) => l' Hl'.
exact: is_filter_lim_unique Hl' Hl.
Qed.

Context {T : Type}.

Lemma iota_filterlim_locally {F} {FF : ProperFilter F} (f : T -> V) l :
  f @ F --> l -> iota (fun x => f @ F --> x) = l.
Proof.
apply iota_is_filter_lim.
Qed.

Lemma iota_filterlimi_locally {F} {FF : ProperFilter F} (f : T -> V -> Prop) l :
  F (fun x => forall y1 y2, f x y1 -> f x y2 -> y1 = y2) ->
  f `@ F --> l ->
  iota (fun x => f `@ F --> x) = l.
Proof.
intros Hf Hl.
apply: iota_unique (Hl) => l' Hl'.
exact: filterlimi_locally_unique Hf Hl' Hl.
Qed.

End CompleteNormedModule1.

(** * Extended Types *)

(** ** Pairs *)


Section prod_ModuleSpace.

Context {K : Ring} {U V : ModuleSpace K}.

Definition prod_scal (x : K) (u : U * V) :=
  (scal x (fst u), scal x (snd u)).

Lemma prod_scal_assoc :
  forall (x y : K) (u : U * V),
  prod_scal x (prod_scal y u) = prod_scal (mult x y) u.
Proof.
intros x y u.
apply (f_equal2 pair) ; apply scal_assoc.
Qed.

Lemma prod_scal_one :
  forall u : U * V,
  prod_scal one u = u.
Proof.
intros [u v].
apply (f_equal2 pair) ; apply scal_one.
Qed.

Lemma prod_scal_distr_l :
  forall (x : K) (u v : U * V),
  prod_scal x (prod_plus u v) = prod_plus (prod_scal x u) (prod_scal x v).
Proof.
intros x u v.
apply (f_equal2 pair) ; apply scal_distr_l.
Qed.

Lemma prod_scal_distr_r :
  forall (x y : K) (u : U * V),
  prod_scal (plus x y) u = prod_plus (prod_scal x u) (prod_scal y u).
Proof.
intros x y u.
apply (f_equal2 pair) ; apply scal_distr_r.
Qed.

End prod_ModuleSpace.

Definition prod_ModuleSpace_mixin (K : Ring) (U V : ModuleSpace K) :=
  ModuleSpace.Mixin K _ _ (@prod_scal_assoc K U V) prod_scal_one prod_scal_distr_l prod_scal_distr_r.

Canonical prod_ModuleSpace (K : Ring) (U V : ModuleSpace K) :=
  ModuleSpace.Pack K (U * V) (ModuleSpace.Class _ _ _ (prod_ModuleSpace_mixin K U V)) (U * V).

Canonical prod_NormedModuleAux (K : AbsRing) (U V : NormedModuleAux K) :=
  NormedModuleAux.Pack K (U * V) (NormedModuleAux.Class _ _ (ModuleSpace.class K _) (Uniform.class (prod_uniformType U V))) (U * V).

Lemma sqrt_plus_sqr :
  forall x y : R, Rmax (Rabs x) (Rabs y) <= sqrt (x ^ 2 + y ^ 2) <= sqrt 2 * Rmax (Rabs x) (Rabs y).
Proof.
intros x y.
split.
- rewrite -!sqrt_Rsqr_abs.
  apply Rmax_case ; apply sqrt_le_1_alt, Rminus_le_0 ;
  rewrite /Rsqr /= ; ring_simplify ; by apply pow2_ge_0.
- apply Rmax_case_strong ; intros H0 ;
  rewrite -!sqrt_Rsqr_abs ;
  rewrite -?sqrt_mult ;
  try (by apply Rle_0_sqr) ;
  try (by apply Rlt_le, Rlt_0_2) ;
  apply sqrt_le_1_alt ; simpl ; [ rewrite Rplus_comm | ] ;
  rewrite /Rsqr ; apply Rle_minus_r ; ring_simplify ;
  apply Rsqr_le_abs_1 in H0 ; by rewrite /pow !Rmult_1_r.
Qed.

Section prod_NormedModule.

Context {K : AbsRing} {U V : NormedModule K}.

Definition prod_norm (x : U * V) :=
  sqrt (norm (fst x) ^ 2 + norm (snd x) ^ 2).

Lemma prod_norm_triangle :
  forall x y : U * V,
  prod_norm (plus x y) <= prod_norm x + prod_norm y.
Proof.
intros [xu xv] [yu yv].
rewrite /prod_norm /= !Rmult_1_r.
apply Rle_trans with (sqrt (Rsqr (norm xu + norm yu) + Rsqr (norm xv + norm yv))).
- apply sqrt_le_1_alt.
  apply Rplus_le_compat.
  apply Rsqr_le_abs_1.
  rewrite -> 2!Rabs_pos_eq.
  apply: norm_triangle.
  apply Rplus_le_le_0_compat ; apply norm_ge_0.
  apply norm_ge_0.
  apply Rsqr_le_abs_1.
  rewrite -> 2!Rabs_pos_eq.
  apply: norm_triangle.
  apply Rplus_le_le_0_compat ; apply norm_ge_0.
  apply norm_ge_0.
- apply Rsqr_incr_0_var.
  apply Rminus_le_0.
  unfold Rsqr ; simpl ; ring_simplify.
  rewrite /pow ?Rmult_1_r.
  rewrite ?sqrt_sqrt ; ring_simplify.
  replace (-2 * norm xu * norm yu - 2 * norm xv * norm yv)
    with (-(2 * (norm xu * norm yu + norm xv * norm yv))) by ring.
  rewrite Rmult_assoc -sqrt_mult.
  rewrite Rplus_comm.
  apply -> Rminus_le_0.
  apply Rmult_le_compat_l.
  apply Rlt_le, Rlt_0_2.
  apply Rsqr_incr_0_var.
  apply Rminus_le_0.
  rewrite /Rsqr ?sqrt_sqrt ; ring_simplify.
  replace (norm xu ^ 2 * norm yv ^ 2 - 2 * norm xu * norm xv * norm yu * norm yv + norm xv ^ 2 * norm yu ^ 2)
    with ((norm xu * norm yv - norm xv * norm yu) ^ 2) by ring.
  apply pow2_ge_0.
  repeat apply Rplus_le_le_0_compat ; apply Rmult_le_pos ; apply pow2_ge_0.
  apply sqrt_pos.
  apply Rplus_le_le_0_compat ; apply Rle_0_sqr.
  apply Rplus_le_le_0_compat ; apply Rle_0_sqr.
  replace (norm xu ^ 2 + 2 * norm xu * norm yu + norm yu ^ 2 + norm xv ^ 2 + 2 * norm xv * norm yv + norm yv ^ 2)
    with ((norm xu + norm yu) ^ 2 + (norm xv + norm yv) ^ 2) by ring.
  apply Rplus_le_le_0_compat ; apply pow2_ge_0.
  apply Rplus_le_le_0_compat ; apply pow2_ge_0.
  apply Rplus_le_le_0_compat ; apply pow2_ge_0.
  apply Rplus_le_le_0_compat ; apply sqrt_pos.
Qed.

Lemma prod_norm_scal :
  forall (l : K) (x : U * V),
  prod_norm (scal l x) <= abs l * prod_norm x.
Proof.
intros l [xu xv].
rewrite /prod_norm /= -(sqrt_Rsqr (abs l)).
2: apply abs_ge_0.
rewrite !Rmult_1_r.
rewrite -sqrt_mult.
2: apply Rle_0_sqr.
apply sqrt_le_1_alt.
rewrite Rmult_plus_distr_l.
unfold Rsqr.
apply Rplus_le_compat.
replace (abs l * abs l * (norm xu * norm xu)) with ((abs l * norm xu) * (abs l * norm xu)) by ring.
apply Rmult_le_compat.
apply norm_ge_0.
apply norm_ge_0.
exact (norm_scal l xu).
exact (norm_scal l xu).
replace (abs l * abs l * (norm xv * norm xv)) with ((abs l * norm xv) * (abs l * norm xv)) by ring.
apply Rmult_le_compat.
apply norm_ge_0.
apply norm_ge_0.
exact (norm_scal l xv).
exact (norm_scal l xv).
apply Rplus_le_le_0_compat ; apply Rle_0_sqr.
Qed.

Lemma prod_norm_compat1 :
  forall (x y : U * V) (eps : R),
  prod_norm (minus y x) < eps -> ball x eps y.
Proof.
intros [xu xv] [yu yv] eps H.
generalize (Rle_lt_trans _ _ _ (proj1 (sqrt_plus_sqr _ _)) H).
rewrite -> !Rabs_pos_eq by apply norm_ge_0.
intros H'.
split ;
  apply norm_compat1 ;
  apply Rle_lt_trans with (2 := H').
apply Rmax_l.
apply Rmax_r.
Qed.

Definition prod_norm_factor :=
  sqrt 2 * Rmax (@norm_factor K U) (@norm_factor K V).

Lemma prod_norm_compat2 :
  forall (x y : U * V) (eps : posreal),
  ball x eps y ->
  prod_norm (minus y x) < prod_norm_factor * eps.
Proof.
intros [xu xv] [yu yv] eps [Bu Bv].
apply Rle_lt_trans with (1 := proj2 (sqrt_plus_sqr _ _)).
simpl.
rewrite Rmult_assoc.
apply Rmult_lt_compat_l.
apply sqrt_lt_R0.
apply Rlt_0_2.
rewrite -> !Rabs_pos_eq by apply norm_ge_0.
rewrite Rmax_mult.
apply Rmax_case.
apply Rlt_le_trans with (2 := Rmax_l _ _).
now apply norm_compat2.
apply Rlt_le_trans with (2 := Rmax_r _ _).
now apply norm_compat2.
apply Rlt_le.
apply cond_pos.
Qed.

Lemma prod_norm_eq_zero :
  forall x : U * V,
  prod_norm x = 0 -> x = zero.
Proof.
intros [xu xv] H.
apply sqrt_eq_0 in H.
rewrite !(pow_Rsqr _ 1) !pow_1 in H.
apply Rplus_sqr_eq_0 in H.
destruct H as [H1 H2].
apply norm_eq_zero in H1.
apply norm_eq_zero in H2.
simpl in H1, H2.
now rewrite H1 H2.
apply Rplus_le_le_0_compat ; apply pow2_ge_0.
Qed.

End prod_NormedModule.

Definition prod_NormedModule_mixin (K : AbsRing) (U V : NormedModule K) :=
  NormedModule.Mixin K _ (@prod_norm K U V) prod_norm_factor prod_norm_triangle
  prod_norm_scal prod_norm_compat1 prod_norm_compat2 prod_norm_eq_zero.

Canonical prod_NormedModule (K : AbsRing) (U V : NormedModule K) :=
  NormedModule.Pack K (U * V) (NormedModule.Class K (U * V) _ (prod_NormedModule_mixin K U V)) (U * V).

Lemma norm_prod {K : AbsRing}
  {U : NormedModule K} {V : NormedModule K}
  (x : U) (y : V) :
  Rmax (norm x) (norm y) <= norm (x,y) <= sqrt 2 * Rmax (norm x) (norm y).
Proof.
  rewrite -(Rabs_pos_eq (norm x)).
  rewrite -(Rabs_pos_eq (norm y)).
  apply sqrt_plus_sqr.
  by apply norm_ge_0.
  by apply norm_ge_0.
Qed.

(** ** Iterated Products *)

Fixpoint Tn (n : nat) (T : Type) : Type :=
  match n with
  | O => unit
  | S n => prod T (Tn n T)
  end.

Notation "[ x1 , .. , xn ]" := (pair x1 .. (pair xn tt) .. ).

Fixpoint mk_Tn {T} (n : nat) (u : nat -> T) : Tn n T :=
  match n with
    | O => (tt : Tn O T)
    | S n => (u O, mk_Tn n (fun n => u (S n)))
  end.
Fixpoint coeff_Tn {T} {n : nat} (x0 : T) : (Tn n T) -> nat -> T :=
  match n with
  | O => fun (_ : Tn O T) (_ : nat) => x0
  | S n' => fun (v : Tn (S n') T) (i : nat) => match i with
           | O => fst v
           | S i => coeff_Tn x0 (snd v) i
           end
  end.
Lemma mk_Tn_bij {T} {n : nat} (x0 : T) (v : Tn n T) :
  mk_Tn n (coeff_Tn x0 v) = v.
Proof.
  induction n ; simpl.
  now apply unit_ind.
  rewrite IHn ; by destruct v.
Qed.
Lemma coeff_Tn_bij {T} {n : nat} (x0 : T) (u : nat -> T) :
  forall i, (i < n)%nat -> coeff_Tn x0 (mk_Tn n u) i = u i.
Proof.
  revert u ; induction n => /= u i Hi.
  by apply lt_n_O in Hi.
  destruct i.
  by [].
  now apply (IHn (fun n => u (S n))), lt_S_n.
Qed.
Lemma coeff_Tn_ext {T} {n : nat} (x1 x2 : T) (v1 v2 : Tn n T) :
  v1 = v2 <-> forall i, (i < n)%nat -> coeff_Tn x1 v1 i = coeff_Tn x2 v2 i.
Proof.
  split.
  + move => -> {v1}.
    induction n => i Hi.
    by apply lt_n_O in Hi.
    destruct i ; simpl.
    by [].
    by apply IHn, lt_S_n.
  + induction n => H.
    apply unit_ind ; move: (v1) ; now apply unit_ind.
    apply injective_projections.
    by apply (H O), lt_O_Sn.
    apply IHn => i Hi.
    by apply (H (S i)), lt_n_S.
Qed.
Lemma mk_Tn_ext {T} (n : nat) (u1 u2 : nat -> T) :
  (forall i, (i < n)%nat -> (u1 i) = (u2 i))
    <-> (mk_Tn n u1) = (mk_Tn n u2).
Proof.
  move: u1 u2 ; induction n ; simpl ; split ; intros.
  by [].
  by apply lt_n_O in H0.
  apply f_equal2.
  by apply H, lt_O_Sn.
  apply IHn => i Hi.
  by apply H, lt_n_S.
  destruct i.
  by apply (f_equal (@fst _ _)) in H.
  move: i {H0} (lt_S_n _ _ H0).
  apply IHn.
  by apply (f_equal (@snd _ _)) in H.
Qed.

(*
Global Instance AbelianGroup_Tn {T} :
  AbelianGroup T -> forall n, AbelianGroup (Tn n T) | 10.
Proof.
  intro GT.
  elim => /= [ | n IH].
  - apply Build_AbelianGroup with (fun _ _ => tt) (fun _ => tt) tt ; auto.
    by apply unit_ind.
  - by apply AbelianGroup_prod.
Defined.

Global Instance MetricBall_Tn :
  forall T, MetricBall T -> forall n, MetricBall (Tn n T) | 10.
Proof.
intros T MT n.
elim: n => [ | n MTn].
by apply Build_MetricBall with (fun _ _ _ => True).
by apply MetricBall_prod.
Defined.

Global Instance VectorSpace_mixin_Tn {T} {K} {FK : Ring K} :
  forall GT : AbelianGroup T,
  VectorSpace_mixin T K GT ->
  forall n, VectorSpace_mixin (Tn n T) K (AbelianGroup_Tn GT n) | 10.
Proof.
  intros GT VV.
  elim => [ | n VVn].
  apply Build_VectorSpace_mixin with (fun _ _ => tt) ; by apply unit_ind.
  by apply VectorSpace_mixin_prod.
Defined.

Global Instance VectorSpace_Tn {T} {K} {FK : Ring K} :
  VectorSpace T K -> forall n, VectorSpace (Tn n T) K | 10.
Proof.
  intros VV n.
  apply Build_VectorSpace with (AbelianGroup_Tn _ n).
  now apply VectorSpace_mixin_Tn, VV.
Defined.

Global Instance NormedVectorSpace_Tn {T} {K} {FK : AbsRing K} :
  NormedVectorSpace T K ->
  forall n, NormedVectorSpace (Tn n T) K | 10.
Proof.
  move => VT.
  elim => [ | n NVTn].
  - econstructor.
    apply Build_NormedVectorSpace_mixin with (fun _ => 0).
    move => _ _.
    rewrite Rplus_0_l ; by apply Rle_refl.
    move => l _ ; rewrite Rmult_0_r ; by apply Rle_refl.
    easy.
    exists [posreal of 1].
    intros x y eps _.
    rewrite Rmult_1_l.
    apply cond_pos.
  - by apply NormedVectorSpace_prod.
Defined.
*)

(** *)

Fixpoint Fn (n : nat) (T U : Type) : Type :=
  match n with
  | O => U
  | S n => T -> Fn n T U
  end.

(*
Global Instance MetricBall_Fn {T M} (n : nat) :
  MetricBall M -> MetricBall (Fn n T M) | 10.
Proof.
  intros MM.
  elim: n => /= [ | n IHn].
  exact MM.
  exact (MetricBall_fct IHn).
Defined.
*)

(** ** Matrices *)

Section Matrices.

Context {T : Type}.

Definition matrix (m n : nat) := Tn m (Tn n T).

Definition coeff_mat {m n : nat} (x0 : T) (A : matrix m n) (i j : nat) :=
  coeff_Tn x0 (coeff_Tn (mk_Tn _ (fun _ => x0)) A i) j.

Definition mk_matrix (m n : nat) (U : nat -> nat -> T) : matrix m n :=
  mk_Tn m (fun i => (mk_Tn n (U i))).

Lemma mk_matrix_bij {m n : nat} (x0 : T) (A : matrix m n) :
  mk_matrix m n (coeff_mat x0 A) = A.
Proof.
  unfold mk_matrix, coeff_mat.
  unfold matrix in A.
  rewrite -{2}(mk_Tn_bij (mk_Tn _ (fun _ => x0)) A).
  apply mk_Tn_ext.
  intros i Hi.
  by rewrite mk_Tn_bij.
Qed.

Lemma coeff_mat_bij {m n : nat} (x0 : T) (u : nat -> nat -> T) :
  forall i j, (i < m)%nat -> (j < n)%nat -> coeff_mat x0 (mk_matrix m n u) i j = u i j.
Proof.
  intros i j Hi Hj.
  unfold mk_matrix, coeff_mat.
  by rewrite 2?coeff_Tn_bij .
Qed.

Lemma coeff_mat_ext_aux {m n : nat} (x1 x2 : T) (v1 v2 : matrix m n) :
  v1 = v2 <-> forall i j, (i < m)%nat -> (j < n)%nat -> (coeff_mat x1 v1 i j) = (coeff_mat x2 v2 i j).
Proof.
  split => Hv.
  + move => i j Hi Hj.
    by repeat apply coeff_Tn_ext.
  + unfold matrix in v1, v2.
    rewrite -(mk_matrix_bij x1 v1) -(mk_matrix_bij x2 v2).
    unfold mk_matrix.
    apply mk_Tn_ext => i Hi.
    apply mk_Tn_ext => j Hj.
    by apply Hv.
Qed.

Lemma coeff_mat_ext {m n : nat} (x0 : T) (v1 v2 : matrix m n) :
  v1 = v2 <-> forall i j, (coeff_mat x0 v1 i j) = (coeff_mat x0 v2 i j).
Proof.
  split.
  by move => ->.
  intro H.
  now apply (coeff_mat_ext_aux x0 x0 v1 v2).
Qed.

Lemma mk_matrix_ext (m n : nat) (u1 u2 : nat -> nat -> T) :
  (forall i j, (i < m)%nat -> (j < n)%nat -> (u1 i j) = (u2 i j))
    <-> (mk_matrix m n u1) = (mk_matrix m n u2).
Proof.
  split => H.
  + apply (mk_Tn_ext m) => i Hi.
    apply (mk_Tn_ext n) => j Hj.
    by apply H.
  + intros i j Hi Hj.
    apply (mk_Tn_ext n).
    apply (mk_Tn_ext m (fun i => mk_Tn n (u1 i)) (fun i => mk_Tn n (u2 i))).
    apply H.
    by [].
    by [].
Qed.

End Matrices.

Section MatrixGroup.

Context {G : AbelianGroup} {m n : nat}.

Definition Mzero := mk_matrix m n (fun i j => @zero G).

Definition Mplus (A B : @matrix G m n) :=
  mk_matrix m n (fun i j => plus (coeff_mat zero A i j) (coeff_mat zero B i j)).

Definition Mopp (A : @matrix G m n) :=
  mk_matrix m n (fun i j => opp (coeff_mat zero A i j)).

Lemma Mplus_comm :
  forall A B : @matrix G m n,
  Mplus A B = Mplus B A.
Proof.
  intros A B.
  apply mk_matrix_ext => i j Hi Hj.
  by apply plus_comm.
Qed.

Lemma Mplus_assoc :
  forall A B C : @matrix G m n,
  Mplus A (Mplus B C) = Mplus (Mplus A B) C.
Proof.
  intros A B C.
  apply mk_matrix_ext => /= i j Hi Hj.
  rewrite ?coeff_mat_bij => //.
  by apply plus_assoc.
Qed.

Lemma Mplus_zero_r :
  forall A : @matrix G m n,
  Mplus A Mzero = A.
Proof.
  intros A.
  apply (coeff_mat_ext_aux zero zero) => i j Hi Hj.
  rewrite ?coeff_mat_bij => //=.
  by apply plus_zero_r.
Qed.

Lemma Mplus_opp_r :
  forall A : @matrix G m n,
  Mplus A (Mopp A) = Mzero.
Proof.
  intros A.
  apply (coeff_mat_ext_aux zero zero) => i j Hi Hj.
  rewrite ?coeff_mat_bij => //=.
  by apply plus_opp_r.
Qed.

Definition matrix_AbelianGroup_mixin :=
  AbelianGroup.Mixin _ _ _ _ Mplus_comm Mplus_assoc Mplus_zero_r Mplus_opp_r.

Canonical matrix_AbelianGroup :=
  AbelianGroup.Pack _ matrix_AbelianGroup_mixin (@matrix G m n).

End MatrixGroup.

Section MatrixRing.

Context {T : Ring}.

Fixpoint Mone_seq i j : T :=
  match i,j with
    | O, O => one
    | O, S _ | S _, O => zero
    | S i, S j => Mone_seq i j end.

Definition Mone {n} : matrix n n :=
  mk_matrix n n Mone_seq.

Lemma Mone_seq_diag :
  forall i j : nat, i = j -> Mone_seq i j = @one T.
Proof.
  move => i j <- {j}.
  by induction i.
Qed.
Lemma Mone_seq_not_diag :
  forall i j : nat, i <> j -> Mone_seq i j = @zero T.
Proof.
  elim => //= [ | i IHi] j Hij ;
  destruct j => //=.
  apply IHi.
  contradict Hij.
  by rewrite Hij.
Qed.

Definition Mmult {n m k} (A : @matrix T n m) (B : @matrix T m k) :=
  mk_matrix n k (fun i j => sum_n (fun l => mult (coeff_mat zero A i l) (coeff_mat zero B l j)) (Nat.pred m)).

Lemma Mmult_assoc {n m k l} :
  forall (A : matrix n m) (B : matrix m k) (C : matrix k l),
  Mmult A (Mmult B C) = Mmult (Mmult A B) C.
Proof.
  intros A B C.
  apply mk_matrix_ext => n' l' Hn' Hl'.
  unfold Mmult at 1.
  - transitivity (sum_n (fun l0 : nat => mult (coeff_mat zero A n' l0)
      (sum_n (fun l1 : nat => mult (coeff_mat zero B l0 l1) (coeff_mat zero C l1 l')) (Nat.pred k))) (Nat.pred m)).
    destruct m ; simpl.
    unfold coeff_mat ; simpl.
    by rewrite 2!mult_zero_l.
    apply sum_n_m_ext_loc ; simpl => m' [ _ Hm'].
    apply f_equal.
    rewrite coeff_mat_bij //.
    by apply le_lt_n_Sm, Hm'.
  - transitivity (sum_n (fun l0 : nat => sum_n
      (fun l1 : nat => mult (coeff_mat zero A n' l0) (mult (coeff_mat zero B l0 l1) (coeff_mat zero C l1 l'))) (Nat.pred k)) (Nat.pred m)).
    destruct m ; simpl.
    rewrite /sum_n !sum_n_n.
    unfold coeff_mat ; simpl.
    rewrite mult_zero_l.
    rewrite sum_n_m_mult_l.
    by rewrite mult_zero_l.
    apply sum_n_m_ext_loc ; simpl => m' [_ Hm'].
    apply sym_eq, sum_n_m_mult_l.
  rewrite sum_n_switch.
  destruct k ; simpl.
  unfold coeff_mat ; simpl.
  rewrite mult_zero_l.
  rewrite /sum_n sum_n_m_mult_r.
  by rewrite mult_zero_r.
  apply sum_n_m_ext_loc => k' [_ Hk'].
  transitivity (mult (sum_n (fun l1 : nat => mult (coeff_mat zero A n' l1) (coeff_mat zero B l1 k')) (Nat.pred m))
    (coeff_mat zero C k' l')).
  rewrite -sum_n_m_mult_r.
  apply sum_n_m_ext_loc => m' [_ Hm'].
  apply mult_assoc.
  apply f_equal2.
  unfold Mmult ; rewrite coeff_mat_bij //.
  by apply le_lt_n_Sm.
  by [].
Qed.

Lemma Mmult_one_r {m n} :
  forall x : matrix m n, Mmult x Mone = x.
Proof.
  intros A.
  rewrite -{2}(mk_matrix_bij zero A).
  apply mk_matrix_ext => /= i j Hi Hj.
  destruct n ; simpl.
  by apply lt_n_O in Hj.
  move: (coeff_mat zero A) => {A} A.
  erewrite sum_n_ext_loc ; last first.
  move => /= k Hk.
  rewrite /Mone coeff_mat_bij //.
  by apply le_lt_n_Sm.
  rewrite /sum_n (sum_n_m_Chasles _ _ j) //.
  2: by apply le_O_n.
  2: by apply lt_n_Sm_le.
  rewrite (sum_n_m_ext_loc _ (fun _ => zero) (S j)).
  rewrite sum_n_m_const_zero plus_zero_r.
  rewrite -/(sum_n _ _).
  destruct j => //.
  by rewrite sum_O Mone_seq_diag // mult_one_r.
  rewrite sum_Sn.
  rewrite (sum_n_ext_loc _ (fun _ => zero)).
  rewrite /sum_n sum_n_m_const_zero plus_zero_l.
  by rewrite Mone_seq_diag // mult_one_r.
  move => k Hk.
  rewrite Mone_seq_not_diag.
  by apply mult_zero_r.
  by apply MyNat.lt_neq, le_lt_n_Sm.
  move => k [Hk _].
  rewrite Mone_seq_not_diag.
  by apply mult_zero_r.
  by apply sym_not_eq, MyNat.lt_neq.
Qed.

Lemma Mmult_one_l {m n} :
  forall x : matrix m n, Mmult Mone x = x.
Proof.
  intros A.
  rewrite -{2}(mk_matrix_bij zero A).
  apply mk_matrix_ext => /= i j Hi Hj.
  destruct m ; simpl.
  by apply lt_n_O in Hi.
  move: (coeff_mat zero A) => {A} A.
  erewrite sum_n_ext_loc ; last first.
  move => /= k Hk.
  rewrite /Mone coeff_mat_bij //.
  by apply le_lt_n_Sm.
  rewrite /sum_n (sum_n_m_Chasles _ _ i) //.
  2: by apply le_O_n.
  2: by apply lt_n_Sm_le.
  rewrite (sum_n_m_ext_loc _ (fun _ => zero) (S i)).
  rewrite sum_n_m_const_zero plus_zero_r.
  rewrite -/(sum_n _ _).
  destruct i => //.
  by rewrite sum_O Mone_seq_diag // mult_one_l.
  rewrite sum_Sn.
  rewrite (sum_n_ext_loc _ (fun _ => zero)).
  rewrite /sum_n sum_n_m_const_zero plus_zero_l.
  by rewrite Mone_seq_diag // mult_one_l.
  move => k Hk.
  rewrite Mone_seq_not_diag.
  by apply mult_zero_l.
  by apply sym_not_eq, MyNat.lt_neq, le_lt_n_Sm.
  move => k [Hk _].
  rewrite Mone_seq_not_diag.
  by apply mult_zero_l.
  by apply MyNat.lt_neq.
Qed.

Lemma Mmult_distr_r {m n k} :
  forall (A B : @matrix T m n) (C : @matrix T n k),
  Mmult (Mplus A B) C = Mplus (Mmult A C) (Mmult B C).
Proof.
  intros A B C.
  unfold Mmult, plus ; simpl ; unfold Mplus.
  apply mk_matrix_ext => i j Hi Hj.
  rewrite ?coeff_mat_bij => //=.
  rewrite -sum_n_m_plus.
  destruct n ; simpl.
  unfold coeff_mat ; simpl.
  by rewrite ?mult_zero_l plus_zero_l.
  apply sum_n_m_ext_loc => l [_ Hl].
  rewrite ?coeff_mat_bij => //=.
  by apply mult_distr_r.
  by apply le_lt_n_Sm.
Qed.

Lemma Mmult_distr_l {m n k} :
  forall (A : @matrix T m n) (B C : @matrix T n k),
  Mmult A (Mplus B C) = Mplus (Mmult A B) (Mmult A C).
Proof.
  intros A B C.
  unfold Mmult, plus ; simpl ; unfold Mplus.
  apply mk_matrix_ext => i j Hi Hj.
  rewrite ?coeff_mat_bij => //=.
  rewrite -sum_n_m_plus.
  destruct n ; simpl.
  unfold coeff_mat ; simpl.
  by rewrite ?mult_zero_l plus_zero_l.
  apply sum_n_m_ext_loc => l [_ Hl].
  rewrite ?coeff_mat_bij => //=.
  by apply mult_distr_l.
  by apply le_lt_n_Sm.
Qed.

Definition matrix_Ring_mixin {n} :=
  Ring.Mixin _ _ _ (@Mmult_assoc n n n n) Mmult_one_r Mmult_one_l Mmult_distr_r Mmult_distr_l.

Canonical matrix_Ring {n} :=
  Ring.Pack (@matrix T n n) (Ring.Class _ _ matrix_Ring_mixin) (@matrix T n n).

Definition matrix_ModuleSpace_mixin {m n} :=
  ModuleSpace.Mixin (@matrix_Ring m) (@matrix_AbelianGroup T m n) Mmult
    Mmult_assoc Mmult_one_l Mmult_distr_l Mmult_distr_r.

Canonical matrix_ModuleSpace {m n} :=
  ModuleSpace.Pack _ (@matrix T m n) (ModuleSpace.Class _ _ _ matrix_ModuleSpace_mixin) (@matrix T m n).

End MatrixRing.

*)

(** * The topology on natural numbers *)

Definition eventually (P : nat -> Prop) :=
  exists N : nat, forall n, (N <= n)%coq_nat -> P n.

Notation "'\oo'" := eventually : classical_set_scope.

Global Instance eventually_filter : ProperFilter eventually.
Proof.
constructor.
  move=> P [N H]; exists N; exact (H _ (le_refl _)).
constructor.
- by exists O.
- move=> P Q [NP HP] [NQ HQ].
  exists (max NP NQ) => n Hn; split.
  by apply/HP/(le_trans _ _ _ _ Hn)/Max.le_max_l.
  by apply/HQ/(le_trans _ _ _ _ Hn)/Max.le_max_r.
- by move=> P Q H [NP HP]; exists NP => n Hn; apply/H/HP.
Qed.

(** * The topology on real numbers *)

(*
Definition R_AbelianGroup_mixin :=
  AbelianGroup.Mixin _ _ _ _ Rplus_comm (fun x y z => sym_eq (Rplus_assoc x y z)) Rplus_0_r Rplus_opp_r.

Canonical R_AbelianGroup :=
  AbelianGroup.Pack _ R_AbelianGroup_mixin R.

Definition R_Ring_mixin :=
  Ring.Mixin _ _ _ (fun x y z => sym_eq (Rmult_assoc x y z)) Rmult_1_r Rmult_1_l Rmult_plus_distr_r Rmult_plus_distr_l.

Canonical R_Ring :=
  Ring.Pack R (Ring.Class _ _ R_Ring_mixin) R.

Lemma Rabs_m1 :
  Rabs (-1) = 1.
Proof.
  rewrite Rabs_Ropp.
  exact Rabs_R1.
Qed.

Definition R_AbsRing_mixin :=
  AbsRing.Mixin _ _ Rabs_R0 Rabs_m1 Rabs_triang (fun x y => Req_le _ _ (Rabs_mult x y)) Rabs_eq_0.

Canonical R_AbsRing :=
  AbsRing.Pack R (AbsRing.Class _ _ R_AbsRing_mixin) R.

Definition R_uniformType_mixin :=
  AbsRing_uniformType_mixin R_AbsRing.

Canonical R_uniformType :=
  UniformType R R_uniformType_mixin.
Canonical R_canonical_filter := CanonicalFilter R R locally.

Definition R_complete_lim (F : (R -> Prop) -> Prop) : R :=
  real (Lub_Rbar (fun x : R => F (ball (x + 1) [posreal of 1]))).

Lemma R_complete_ax1 :
  forall F : (R -> Prop) -> Prop,
  ProperFilter F ->
  (forall eps : posreal, exists x : R, F (ball x eps)) ->
  forall eps : posreal, F (ball (R_complete_lim F) eps).
Proof.
intros F FF HF eps.
unfold R_complete_lim.
generalize (Lub_Rbar_correct (fun x : R => F (ball (x + 1) [posreal of 1]))).
generalize (Lub_Rbar (fun x : R => F (ball (x + 1) [posreal of 1]))).
intros [x| |] [Hx1 Hx2].
-
set (eps' := [posreal of Rmin 2 eps / 2]).
destruct (HF eps') as [z Hz].
assert (H1 : z - Rmin 2 eps / 2 + 1 <= x + 1).
  apply Rplus_le_compat_r.
  apply Hx1.
  revert Hz.
  apply filter_imp.
  unfold ball ; simpl ; intros u Bu.
  apply (Rabs_lt_between' u z) in Bu.
  apply Rabs_lt_between'.
  clear -Bu.
  destruct Bu as [Bu1 Bu2].
  assert (H := Rmin_l 2 eps).
  split ; Fourier.fourier.
assert (H2 : x + 1 <= z + Rmin 2 eps / 2 + 1).
  apply Rplus_le_compat_r.
  apply (Hx2 (Finite _)).
  intros v Hv.
  apply Rbar_not_lt_le => Hlt.
  apply filter_not_empty.
  generalize (filter_and _ _ Hz Hv).
  apply filter_imp.
  unfold ball ; simpl ; intros w [Hw1 Hw2].
  apply (Rabs_lt_between' w z) in Hw1.
  destruct Hw1 as [_ Hw1].
  apply (Rabs_lt_between' w (v + 1)) in Hw2.
  destruct Hw2 as [Hw2 _].
  clear -Hw1 Hw2 Hlt.
  simpl in Hw1, Hw2, Hlt.
  Fourier.fourier.
revert Hz.
apply filter_imp.
unfold ball ; simpl ; intros u Hu.
apply (Rabs_lt_between' u z) in Hu.
apply Rabs_lt_between'.
assert (H3 := Rmin_l 2 eps).
assert (H4 := Rmin_r 2 eps).
clear -H1 H2 Hu H3 H4.
destruct Hu.
split ; Fourier.fourier.
-
  destruct (HF [posreal of 1]) as [y Fy].
  elim (Hx2 (y + 1)).
  intros x Fx.
  apply Rbar_not_lt_le => Hlt.
  apply filter_not_empty.
  generalize (filter_and _ _ Fy Fx).
  apply filter_imp.
  intros z [Hz1 Hz2].
  revert Hlt.
  apply Rbar_le_not_lt.
  apply Rplus_le_reg_r with (-(y - 1)).
  replace (y + 1 + -(y - 1)) with 2 by ring.
  apply Rabs_le_between.
  apply Rlt_le.
  generalize (ball_triangle y z (x + 1) 1 1) => /= H.
  replace (x + -(y - 1)) with ((x + 1) - y) by ring.
  apply H.
  apply Hz1.
  apply ball_sym in Hz2.
  apply Hz2.
-
  destruct (HF [posreal of 1]) as [y Fy].
  elim (Hx1 (y - 1)).
  now replace (y - 1 + 1) with y by ring.
Qed.

Lemma R_complete :
  forall F : (R -> Prop) -> Prop,
  ProperFilter F ->
  (forall eps : posreal, exists x : R, F (ball x eps)) ->
  forall eps : posreal, F (ball (R_complete_lim F) eps).
Proof.
intros F FF.
apply R_complete_ax1.
by apply Proper_StrongProper.
Qed.

Lemma R_complete_ax2 :
  forall F1 F2 : (R -> Prop) -> Prop,
  filter_le F1 F2 -> filter_le F2 F1 ->
  R_complete_lim F1 = R_complete_lim F2.
Proof.
intros F1 F2 H12 H21.
unfold R_complete_lim.
apply f_equal, Lub_Rbar_eqset.
split.
apply H21.
apply H12.
Qed.

Lemma R_complete_close :
  forall F1 F2 : (R -> Prop) -> Prop,
  filter_le F1 F2 -> filter_le F2 F1 ->
  close (R_complete_lim F1) (R_complete_lim F2).
Proof.
intros F1 F2 H12 H21.
replace (R_complete_lim F2) with (R_complete_lim F1).
intros eps.
apply ball_center.
exact: R_complete_ax2.
Qed.

Definition R_completeType_mixin :=
  Complete.Mixin _ R_complete_lim R_complete R_complete_close.

Canonical R_completeType :=
  Complete.Pack R (Complete.Class _ _ R_completeType_mixin) R.

Definition R_ModuleSpace_mixin :=
  AbsRing_ModuleSpace_mixin R_AbsRing.

Canonical R_ModuleSpace :=
  ModuleSpace.Pack _ R (ModuleSpace.Class _ _ _ R_ModuleSpace_mixin) R.

Canonical R_NormedModuleAux :=
  NormedModuleAux.Pack _ R (NormedModuleAux.Class _ _ (ModuleSpace.class _ R_ModuleSpace) (Uniform.class R_uniformType)) R.

Definition R_NormedModule_mixin :=
  AbsRing_NormedModule_mixin R_AbsRing.

Canonical R_NormedModule :=
  NormedModule.Pack _ R (NormedModule.Class _ _ _ R_NormedModule_mixin) R.

Canonical R_CompleteNormedModule :=
  CompleteNormedModule.Pack _ R (CompleteNormedModule.Class R_AbsRing _ (NormedModule.class _ R_NormedModule) R_completeType_mixin) R.

Definition at_left x := within (fun u : R => Rlt u x) (locally x).
Definition at_right x := within (fun u : R => Rlt x u) (locally x).

Global Instance at_right_proper_filter : forall (x : R),
  ProperFilter (at_right x).
Proof.
  constructor.
  intros P [d Hd].
  exists (x + d / 2).
  apply Hd.
  apply @norm_compat1 ; rewrite /norm /minus /plus /opp /= /abs /=.
  ring_simplify (x + d / 2 + - x).
  rewrite Rabs_pos_eq.
  apply Rlt_div_l.
  by apply Rlt_0_2.
  apply Rminus_lt_0 ; ring_simplify ; by apply d.
  apply Rlt_le => //.
  apply Rminus_lt_0 ; ring_simplify => //.
  apply within_filter, locally_filter.
Qed.
Global Instance at_left_proper_filter : forall (x : R),
  ProperFilter (at_left x).
Proof.
  constructor.
  intros P [d Hd].
  exists (x - d / 2).
  apply Hd.
  apply @norm_compat1 ; rewrite /norm /minus /plus /opp /= /abs /=.
  ring_simplify (x - d / 2 + - x).
  rewrite Rabs_Ropp Rabs_pos_eq.
  apply Rlt_div_l.
  by apply Rlt_0_2.
  apply Rminus_lt_0 ; ring_simplify ; by apply d.
  apply Rlt_le => //.
  apply Rminus_lt_0 ; ring_simplify=> //.
  apply within_filter, locally_filter.
Qed.

(* *)

Lemma sum_n_Reals : forall a N, sum_n a N = sum_f_R0 a N.
Proof.
  intros a; induction N; simpl.
  apply sum_n_n.
  by rewrite sum_Sn IHN.
Qed.
Lemma sum_n_m_Reals a n m : (n <= m)%nat -> sum_n_m a n m = sum_f n m a.
Proof.
  induction m => //= Hnm.
  apply le_n_O_eq in Hnm.
  by rewrite -Hnm sum_n_n /=.
  case: (le_dec n m) => H.
  rewrite sum_n_Sm // IHm //.
  rewrite sum_f_n_Sm //.
  replace n with (S m).
  rewrite sum_n_n.
  by rewrite /sum_f minus_diag /=.
  apply le_antisym => //.
  apply not_le in H.
  by apply lt_le_S.
Qed.

Lemma sum_n_m_const (n m : nat) (a : R) :
  sum_n_m (fun _ => a) n m = INR (S m - n) * a.
Proof.
  rewrite /sum_n_m /iter_nat (iter_const _ a).
  by rewrite -{2}(seq.size_iota n (S m - n)).
Qed.
Lemma sum_n_const (n : nat) (a : R) :
  sum_n (fun _ => a) n = INR (S n) * a.
Proof.
  by rewrite /sum_n sum_n_m_const -minus_n_O.
Qed.

Lemma norm_sum_n_m {K : AbsRing} {V : NormedModule K} (a : nat -> V) (n m : nat) :
  norm (sum_n_m a n m) <= sum_n_m (fun n => norm (a n)) n m.
Proof.
  case: (le_dec n m) => Hnm.
  elim: m n a Hnm => /= [ | m IH] n a Hnm.
  apply le_n_O_eq in Hnm.
  rewrite -Hnm !sum_n_n.
  by apply Rle_refl.
  destruct n.
  rewrite /sum_n !sum_n_Sm ; try by apply le_O_n.
  eapply Rle_trans.
  apply norm_triangle.
  apply Rplus_le_compat_r, IH, le_O_n.
  rewrite -!sum_n_m_S.
  apply IH.
  by apply le_S_n.
  apply not_le in Hnm.
  rewrite !sum_n_m_zero // norm_zero.
  by apply Rle_refl.
Qed.

Lemma sum_n_m_le (a b : nat -> R) (n m : nat) :
  (forall k, a k <= b k)
  -> sum_n_m a n m <= sum_n_m b n m.
Proof.
  intros H.
  case: (le_dec n m) => Hnm.
  elim: m n a b Hnm H => /= [ | m IH] n a b Hnm H.
  apply le_n_O_eq in Hnm ; rewrite -Hnm.
  rewrite !sum_n_n ; by apply H.
  destruct n.
  rewrite !sum_n_Sm ; try by apply le_O_n.
  apply Rplus_le_compat.
  apply IH => // ; by apply le_O_n.
  by apply H.
  rewrite -!sum_n_m_S.
  apply IH => //.
  by apply le_S_n.
  apply not_le in Hnm.
  rewrite !sum_n_m_zero //.
  by apply Rle_refl.
Qed.

Lemma pow_n_pow :
  forall (x : R) k, pow_n x k = x^k.
Proof.
intros x; induction k; simpl.
easy.
now rewrite IHk.
Qed.

(** Continuity of norm *)

Lemma filterlim_norm {K : AbsRing} {V : NormedModule K} :
  forall (x : V), norm @ x --> (norm x).
Proof.
  intros x.
  apply (filterlim_filter_le_1 _ (locally_le_locally_norm x)).
  apply/filterlim_locally => eps /=.
  exists eps ; move => /= y Hy.
  apply Rle_lt_trans with (2 := Hy).
  apply norm_triangle_inv.
Qed.

Lemma filterlim_norm_zero {U} {K : AbsRing} {V : NormedModule K}
  {F : set (set U)} {FF : Filter F} (f : U -> V) :
  (fun x => norm (f x)) @ F --> 0
  -> f @ F --> (zero (G := V)).
Proof.
  intros Hf.
  apply filterlim_locally_ball_norm => eps.
  generalize (proj1 (filterlim_locally_ball_norm _ _) Hf eps) ;
  unfold ball_norm ; simpl.
  apply filter_imp => /= x.
  rewrite !minus_zero_r {1}/norm /= /abs /= Rabs_pos_eq //.
  by apply norm_ge_0.
Qed.

Canonical eventually_filter_source X :=
  @CanonicalFilterSource X _ nat (fun f => f @ \oo).

Lemma filterlim_bounded {K : AbsRing} {V : NormedModule K} (a : nat -> V) :
  (exists x : V, a --> x)
 -> {M : R | forall n, norm (a n) <= M}.
Proof.
  intros Ha.
  assert (exists x : R, (fun n => norm (a n)) --> x).
    destruct Ha as [l Hl].
    exists (norm l).
    eapply filterlim_comp.
    by apply Hl.
    by apply filterlim_norm.
  clear Ha.

  destruct (LPO_ub_dec (fun n => norm (a n))) as [[M HM]|HM].
  now exists M.
  elimtype False.
  case: H => l Hl.
  assert (H := proj1 (filterlim_locally (F := eventually) _ l) Hl [posreal of 1]).
  clear Hl ; simpl in H ; rewrite /ball /= /AbsRing_ball in H.
  destruct H as [N HN].
  specialize (HM (seq.foldr Rmax (1 + norm l) (seq.map (fun n => norm (a n)) (seq.iota 0 N)))).
  destruct HM as [n Hn].
  revert Hn.
  apply Rle_not_lt.
  elim: N a n HN => /=[ |N IH] a n HN.
  rewrite Rplus_comm.
  apply Rlt_le, Rabs_lt_between'.
  eapply Rle_lt_trans, HN.
  rewrite /abs /=.
  eapply Rle_trans, (norm_triangle_inv (norm (a n)) l).
  apply Req_le, f_equal, f_equal2 => //.
  apply sym_eq, Rabs_pos_eq, norm_ge_0.
  by apply le_O_n.
  case: n => [ | n].
  apply Rmax_l.
  eapply Rle_trans, Rmax_r.
  eapply Rle_trans.
  apply (IH (fun n => a (S n))).
  intros k Hk.
  apply HN.
  by apply le_n_S.
  clear.
  apply Req_le.
  elim: N 0%nat => /=[ |N IH] n0.
  by [].
  apply f_equal.
  apply IH.
Qed.

(** Some open sets of [R] *)

Lemma open_lt :
  forall y : R, open (fun u : R => u < y).
Proof.
intros y x Hxy.
apply Rminus_lt_0 in Hxy.
exists (mkposreal _ Hxy).
intros z Bz.
replace y with (x + (y - x)) by ring.
apply Rabs_lt_between'.
apply Bz.
Qed.

Lemma open_gt :
  forall y : R, open (fun u : R => y < u).
Proof.
intros y x Hxy.
apply Rminus_lt_0 in Hxy.
exists (mkposreal _ Hxy).
intros z Bz.
replace y with (x - (x - y)) by ring.
apply Rabs_lt_between'.
apply Bz.
Qed.

Lemma open_neq :
  forall y : R, open (fun u : R => u <> y).
Proof.
intros y.
apply (open_ext (fun u => u < y \/ y < u)).
intros u.
split.
apply Rlt_dichotomy_converse.
apply Rdichotomy.
apply open_or.
apply open_lt.
apply open_gt.
Qed.

(** Some closed sets of [R] *)

Lemma closed_le :
  forall y : R, closed (fun u : R => u <= y).
Proof.
intros y.
apply closed_ext with (fun u => not (Rlt y u)).
intros x.
split.
apply Rnot_lt_le.
apply Rle_not_lt.
apply closed_not.
apply open_gt.
Qed.

Lemma closed_ge :
  forall y : R, closed (fun u : R => y <= u).
Proof.
intros y.
apply closed_ext with (fun u => not (Rlt u y)).
intros x.
split.
apply Rnot_lt_le.
apply Rle_not_lt.
apply closed_not.
apply open_lt.
Qed.

Lemma closed_eq :
  forall y : R, closed (fun u : R => u = y).
Proof.
intros y.
apply closed_ext with (fun u => not (u <> y)).
intros x.
destruct (Req_dec x y) ; intuition.
apply closed_not.
apply open_neq.
Qed.

(** Local properties in [R] *)

Lemma locally_interval (P : R -> Prop) (x : R) (a b : Rbar) :
  Rbar_lt a x -> Rbar_lt x b ->
  (forall (y : R), Rbar_lt a y -> Rbar_lt y b -> P y) ->
  locally x P.
Proof.
  move => Hax Hxb Hp.
  case: (Rbar_lt_locally _ _ _ Hax Hxb) => d Hd.
  exists d => y Hy.
  now apply Hp ; apply Hd.
Qed.

(** * Topology on [R]² *)

Definition locally_2d (P : R -> R -> Prop) x y :=
  exists delta : posreal, forall u v, Rabs (u - x) < delta -> Rabs (v - y) < delta -> P u v.

Lemma locally_2d_locally :
  forall P x y,
  locally_2d P x y <-> locally (x,y) (fun z => P (fst z) (snd z)).
Proof.
intros P x y.
split ; intros [d H] ; exists d.
- simpl.
  intros [u v] H'.
  now apply H ; apply H'.
- intros u v Hu Hv.
  apply (H (u,v)).
  by split.
Qed.

Lemma locally_2d_impl_strong :
  forall (P Q : R -> R -> Prop) x y, locally_2d (fun u v => locally_2d P u v -> Q u v) x y ->
  locally_2d P x y -> locally_2d Q x y.
Proof.
intros P Q x y Li LP.
apply locally_2d_locally in Li.
apply locally_2d_locally in LP.
apply locally_locally in LP.
apply locally_2d_locally.
generalize (filter_and _ _ Li LP).
apply filter_imp.
intros [u v] [H1 H2].
apply H1.
now apply locally_2d_locally.
Qed.

Lemma locally_2d_singleton (P : R -> R -> Prop) x y : locally_2d P x y -> P x y.
Proof.
move/locally_2d_locally => LP.
by apply locally_singleton with (1 := LP).
Qed.

Lemma locally_2d_impl :
  forall (P Q : R -> R -> Prop) x y, locally_2d (fun u v => P u v -> Q u v) x y ->
  locally_2d P x y -> locally_2d Q x y.
Proof.
intros P Q x y (d,H).
apply locally_2d_impl_strong.
exists d => u v Hu Hv Hp.
apply H => //.
now apply locally_2d_singleton.
Qed.

Lemma locally_2d_forall :
  forall (P : R -> R -> Prop) x y, (forall u v, P u v) -> locally_2d P x y.
Proof.
intros P x y Hp.
now exists [posreal of 1] => u v _ _.
Qed.

Lemma locally_2d_and :
  forall (P Q : R -> R -> Prop) x y, locally_2d P x y -> locally_2d Q x y ->
  locally_2d (fun u v => P u v /\ Q u v) x y.
Proof.
intros P Q x y H.
apply: locally_2d_impl.
apply: locally_2d_impl H.
apply locally_2d_forall.
now split.
Qed.

Lemma locally_2d_align :
  forall (P Q : R -> R -> Prop) x y,
  ( forall eps : posreal, (forall u v, Rabs (u - x) < eps -> Rabs (v - y) < eps -> P u v) ->
    forall u v, Rabs (u - x) < eps -> Rabs (v - y) < eps -> Q u v ) ->
  locally_2d P x y -> locally_2d Q x y.
Proof.
intros P Q x y K (d,H).
exists d => u v Hu Hv.
now apply (K d).
Qed.

Lemma locally_2d_1d_const_x :
  forall (P : R -> R -> Prop) x y,
  locally_2d P x y ->
  locally y (fun t => P x t).
Proof.
intros P x y (d,Hd).
exists d; intros z Hz.
apply Hd.
rewrite Rminus_eq_0 Rabs_R0; apply cond_pos.
exact Hz.
Qed.

Lemma locally_2d_1d_const_y :
  forall (P : R -> R -> Prop) x y,
  locally_2d P x y ->
  locally x (fun t => P t y).
Proof.
intros P x y (d,Hd).
exists d; intros z Hz.
apply Hd.
exact Hz.
rewrite Rminus_eq_0 Rabs_R0; apply cond_pos.
Qed.

Lemma locally_2d_1d_strong :
  forall (P : R -> R -> Prop) x y,
  locally_2d P x y ->
  locally_2d (fun u v => forall t, 0 <= t <= 1 ->
    locally t (fun z => locally_2d P (x + z * (u - x)) (y + z * (v - y)))) x y.
Proof.
intros P x y.
apply locally_2d_align => eps HP u v Hu Hv t Ht.
assert (Zm: 0 <= Rmax (Rabs (u - x)) (Rabs (v - y))).
apply Rmax_case ; apply Rabs_pos.
destruct Zm as [Zm|Zm].
(* *)
assert (H1: Rmax (Rabs (u - x)) (Rabs (v - y)) < eps).
now apply Rmax_case.
set (d1 := mkposreal _ (Rlt_Rminus _ _ H1)).
assert (H2: 0 < d1 / 2 / Rmax (Rabs (u - x)) (Rabs (v - y))).
apply Rmult_lt_0_compat => //.
now apply Rinv_0_lt_compat.
set (d2 := mkposreal _ H2).
exists d2 => z Hz.
exists [posreal of d1 / 2] => p q Hp Hq.
apply HP.
(* . *)
replace (p - x) with (p - (x + z * (u - x)) + (z - t + t) * (u - x)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
replace (pos eps) with (d1 / 2 + (eps - d1 / 2)) by ring.
apply Rplus_lt_le_compat with (1 := Hp).
rewrite Rabs_mult.
apply Rle_trans with ((d2 + 1) * Rmax (Rabs (u - x)) (Rabs (v - y))).
apply Rmult_le_compat.
apply Rabs_pos.
apply Rabs_pos.
apply Rle_trans with (1 := Rabs_triang _ _).
apply Rplus_le_compat.
now apply Rlt_le.
now rewrite Rabs_pos_eq.
apply Rmax_l.
rewrite /d2 /d1 /=.
field_simplify.
apply Rle_refl.
now apply Rgt_not_eq.
(* . *)
replace (q - y) with (q - (y + z * (v - y)) + (z - t + t) * (v - y)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
replace (pos eps) with (d1 / 2 + (eps - d1 / 2)) by ring.
apply Rplus_lt_le_compat with (1 := Hq).
rewrite Rabs_mult.
apply Rle_trans with ((d2 + 1) * Rmax (Rabs (u - x)) (Rabs (v - y))).
apply Rmult_le_compat.
apply Rabs_pos.
apply Rabs_pos.
apply Rle_trans with (1 := Rabs_triang _ _).
apply Rplus_le_compat.
now apply Rlt_le.
now rewrite Rabs_pos_eq.
apply Rmax_r.
rewrite /d2 /d1 /=.
field_simplify.
apply Rle_refl.
now apply Rgt_not_eq.
(* *)
apply filter_forall => z.
exists eps => p q.
replace (u - x) with 0.
replace (v - y) with 0.
rewrite Rmult_0_r 2!Rplus_0_r.
apply HP.
apply sym_eq.
apply Rabs_eq_0.
apply Rle_antisym.
rewrite Zm.
apply Rmax_r.
apply Rabs_pos.
apply sym_eq.
apply Rabs_eq_0.
apply Rle_antisym.
rewrite Zm.
apply Rmax_l.
apply Rabs_pos.
Qed.

Lemma locally_2d_1d (P : R -> R -> Prop) x y :
  locally_2d P x y ->
  locally_2d (fun u v => forall t, 0 <= t <= 1 -> locally_2d P (x + t * (u - x)) (y + t * (v - y))) x y.
Proof.
move/locally_2d_1d_strong.
apply: locally_2d_impl.
apply locally_2d_forall => u v H t Ht.
specialize (H t Ht).
have : locally t (fun z => locally_2d P (x + z * (u - x)) (y + z * (v - y))) by [].
by apply: locally_singleton.
Qed.

Lemma locally_2d_ex_dec :
  forall P x y,
  (forall x y, P x y \/ ~P x y) ->
  locally_2d P x y ->
  {d : posreal | forall u v, Rabs (u-x) < d -> Rabs (v-y) < d -> P u v}.
Proof.
intros P x y P_dec H.
destruct (locally_ex_dec (x, y) (fun z => P (fst z) (snd z))) as [d Hd].
- now intros [u v].
- destruct H as [e H].
  exists e.
  intros [u v] Huv.
  apply H.
  apply Huv.
  apply Huv.
exists d.
intros u v Hu Hv.
apply (Hd (u, v)).
simpl.
now split.
Qed.

(** * Some Topology on [Rbar] *)

Definition Rbar_locally' (a : Rbar) (P : R -> Prop) :=
  match a with
    | Finite a => locally' a P
    | +oo => exists M : R, forall x, M < x -> P x
    | -oo => exists M : R, forall x, x < M -> P x
  end.
Definition Rbar_locally (a : Rbar) (P : R -> Prop) :=
  match a with
    | Finite a => locally a P
    | +oo => exists M : R, forall x, M < x -> P x
    | -oo => exists M : R, forall x, x < M -> P x
  end.

Canonical Rbar_canonical_filter := CanonicalFilter R Rbar (Rbar_locally).

Global Instance Rbar_locally'_filter :
  forall x, ProperFilter (Rbar_locally' x).
Proof.
intros [x| |] ; (constructor ; [idtac | constructor]).
- intros P [eps HP].
  exists (x + eps / 2).
  apply HP.
    rewrite /ball /= /AbsRing_ball /abs /minus /plus /opp /=.
    ring_simplify (x + eps / 2 + - x).
    rewrite Rabs_pos_eq.
      apply Rminus_lt_0.
      by rewrite (_ : _ - _ = eps / 2)//; field.
    exact: Rlt_le.
  apply Rgt_not_eq, Rminus_lt_0 ; ring_simplify => //.
- now exists [posreal of 1].
- intros P Q [dP HP] [dQ HQ].
  exists [posreal of Rmin dP dQ].
  simpl.
  intros y Hy H.
  split.
  apply HP with (2 := H).
  apply Rlt_le_trans with (1 := Hy).
  apply Rmin_l.
  apply HQ with (2 := H).
  apply Rlt_le_trans with (1 := Hy).
  apply Rmin_r.
- intros P Q H [dP HP].
  exists dP.
  intros y Hy H'.
  apply H.
  now apply HP.
- intros P [N HP].
  exists (N + 1).
  apply HP.
  apply Rlt_plus_1.
- now exists 0.
- intros P Q [MP HP] [MQ HQ].
  exists (Rmax MP MQ).
  intros y Hy.
  split.
  apply HP.
  apply Rle_lt_trans with (2 := Hy).
  apply Rmax_l.
  apply HQ.
  apply Rle_lt_trans with (2 := Hy).
  apply Rmax_r.
- intros P Q H [dP HP].
  exists dP.
  intros y Hy.
  apply H.
  now apply HP.
- intros P [N HP].
  exists (N - 1).
  apply HP.
  apply Rlt_minus_l, Rlt_plus_1.
- now exists 0.
- intros P Q [MP HP] [MQ HQ].
  exists (Rmin MP MQ).
  intros y Hy.
  split.
  apply HP.
  apply Rlt_le_trans with (1 := Hy).
  apply Rmin_l.
  apply HQ.
  apply Rlt_le_trans with (1 := Hy).
  apply Rmin_r.
- intros P Q H [dP HP].
  exists dP.
  intros y Hy.
  apply H.
  now apply HP.
Qed.

Global Instance Rbar_locally_filter :
  forall x, ProperFilter (Rbar_locally x).
Proof.
intros [x| |].
- apply locally_filter.
- exact (Rbar_locally'_filter +oo).
- exact (Rbar_locally'_filter -oo).
Qed.

(** Open sets in [Rbar] *)

Lemma open_Rbar_lt :
  forall y, open (fun u : R => Rbar_lt u y).
Proof.
intros [y| |].
- apply open_lt.
- apply open_true.
- apply open_false.
Qed.

Lemma open_Rbar_gt :
  forall y, open (fun u : R => Rbar_lt y u).
Proof.
intros [y| |].
- apply open_gt.
- apply open_false.
- apply open_true.
Qed.

Lemma open_Rbar_lt' :
  forall x y, Rbar_lt x y -> Rbar_locally x (fun u => Rbar_lt u y).
Proof.
intros [x| |] y Hxy.
- now apply open_Rbar_lt.
- easy.
- destruct y as [y| |].
  now exists y.
  now apply filter_forall.
  easy.
Qed.

Lemma open_Rbar_gt' :
  forall x y, Rbar_lt y x -> Rbar_locally x (fun u => Rbar_lt y u).
Proof.
intros [x| |] y Hxy.
- now apply open_Rbar_gt.
- destruct y as [y| |].
  now exists y.
  easy.
  now apply filter_forall.
- now destruct y as [y| |].
Qed.

Lemma Rbar_locally'_le x : Rbar_locally' x --> Rbar_locally x.
Proof. by move: x; move=> [x| | ] P [eps HP]; exists eps => *; apply: HP. Qed.

Lemma Rbar_locally'_le_finite (x : R) : Rbar_locally' x --> locally x.
Proof. by move=> P [eps HP]; exists eps => *; apply: HP. Qed.

(** * Some limits on real functions *)

Definition Rbar_loc_seq (x : Rbar) (n : nat) := match x with
    | Finite x => x + / (INR n + 1)
    | +oo => INR n
    | -oo => - INR n
  end.

Lemma filterlim_Rbar_loc_seq  x : Rbar_loc_seq x --> Rbar_locally' x.
Proof.
  intros P.
  unfold Rbar_loc_seq.
  case: x => /= [x | | ] [delta Hp].
(* x \in R *)
  case: (nfloor_ex (/delta)) => [ | N [_ HN]].
  by apply Rlt_le, Rinv_0_lt_compat, delta.
  exists N => n Hn.
  apply Hp ; simpl.
  rewrite /ball /= /AbsRing_ball /abs /minus /plus /opp /=.
  ring_simplify (x + / (INR n + 1) + - x).
  rewrite Rabs_pos_eq.
  rewrite -(Rinv_involutive delta).
  apply Rinv_lt_contravar.
  apply Rmult_lt_0_compat.
  apply Rinv_0_lt_compat.
  by apply delta.
  exact: INRp1_pos.
  apply Rlt_le_trans with (1 := HN).
  by apply Rplus_le_compat_r, le_INR.
  by apply Rgt_not_eq, delta.
  by apply Rlt_le, RinvN_pos.
  apply Rgt_not_eq, Rminus_lt_0.
  ring_simplify.
  by apply RinvN_pos.
(* x = +oo *)
  case: (nfloor_ex (Rmax 0 delta)) => [ | N [_ HN]].
  by apply Rmax_l.
  exists (S N) => n Hn.
  apply Hp.
  apply Rle_lt_trans with (1 := Rmax_r 0 _).
  apply Rlt_le_trans with (1 := HN).
  rewrite -S_INR ; by apply le_INR.
(* x = -oo *)
  case: (nfloor_ex (Rmax 0 (-delta))) => [ | N [_ HN]].
  by apply Rmax_l.
  exists (S N) => n Hn.
  apply Hp.
  rewrite -(Ropp_involutive delta).
  apply Ropp_lt_contravar.
  apply Rle_lt_trans with (1 := Rmax_r 0 _).
  apply Rlt_le_trans with (1 := HN).
  rewrite -S_INR ; by apply le_INR.
Qed.


Lemma continuity_pt_locally f x :
  continuity_pt f x <->
  forall eps : posreal, locally x (fun u => Rabs (f u - f x) < eps).
Proof.
split.
intros H eps.
move: (H eps (cond_pos eps)) => {H} [d [H1 H2]].
rewrite /= /R_dist /D_x /no_cond in H2.
exists (mkposreal d H1) => y H.
destruct (Req_dec x y) as [<-|Hxy].
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
by apply H2.
intros H eps He.
move: (H (mkposreal _ He)) => {H} [d H].
exists d.
split.
apply cond_pos.
intros h [Zh Hh].
exact: H.
Qed.

Lemma continuity_pt_filterlim (f : R -> R) (x : R) :
  continuity_pt f x <-> f @ x --> f x.
Proof.
eapply iff_trans.
apply continuity_pt_locally.
apply iff_sym.
exact (filterlim_locally f (f x)).
Qed.

Lemma continuity_ptE (f : R -> R) (x : R) :
 continuity_pt f x <-> {for x, continuous f}.
Proof. exact: continuity_pt_filterlim. Qed.

Lemma continuous_withinNx {U V : uniformType} (Ueqdec : forall x y : U, x = y \/ x <> y)
  (f : U -> V) x :
  {for x, continuous f} <-> f @ locally' x --> f x.
Proof.
split=> - cfx P /= fxP.
  by rewrite appfilter; apply filter_le_within; apply/cfx.
 (* :BUG: ssr apply: does not work,
    because the type of the filter is not infered *)
have /= := cfx P fxP; rewrite !appfilter => /filterP[//= Q Qx QP].
apply/filterP; exists (fun y => y <> x -> Q y) => // y Qy.
by have [->|/Qy /QP //] := Ueqdec y x; apply: locally_singleton.
Qed.

Lemma continuity_pt_filterlim' f x :
   continuity_pt f x <-> f @ locally' x --> f x.
Proof. by rewrite continuity_ptE continuous_withinNx //; exact: Req_dec. Qed.


Lemma continuity_pt_locally' f x :
  continuity_pt f x <->
  forall eps : posreal, locally' x (fun u => Rabs (f u - f x) < eps).
Proof.
rewrite continuity_ptE continuous_withinNx; last exact: Req_dec.
exact: filterlim_locally.
Qed.

Lemma locally_pt_comp (P : R -> Prop) (f : R -> R) (x : R) :
  locally (f x) P -> continuity_pt f x ->
  locally x (fun x => P (f x)).
Proof.
intros Lf Cf.
apply continuity_pt_filterlim in Cf.
now apply Cf.
Qed.
*)
