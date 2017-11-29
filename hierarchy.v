(* cara (c) 2017 Inria and AIST. License: CeCILL-C.                           *)
Require Import Reals.
From Coq Require Import ssreflect ssrfun ssrbool.
Require Import Rcomplements Rbar Markov Iter Lub.
From mathcomp Require Import ssrnat eqtype choice ssralg ssrnum.
From SsrReals Require Import boolp reals.
Require Import Rstruct set R_ext.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Def Num.Theory.

Delimit Scope R_scope with coqR.
Delimit Scope real_scope with real.
Local Close Scope R_scope.
Local Open Scope ring_scope.
Local Open Scope real_scope.
Local Open Scope classical_set_scope.

(* Enrico's trick for tc resolution in have *)
Notation "!! x" := (ltac:(refine x)) (at level 100, only parsing).
Class infer (P : Prop) := Infer : P.
Hint Mode infer ! : typeclass_instances.

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

Lemma filter_of_filterE T (F : set (set T)) : [filter of F] = F.
Proof. by []. Qed.

Lemma filter_of_genericE X T (F : canonical_filter_on X T) :
  [filter of canonical_filter_term F] = canonical_term_filter F.
Proof. by []. Qed.

Definition filter_ofE := (filter_of_filterE, filter_of_genericE).

Section Near.

Local Notation "{ 'all1' P }" := (forall x, P x : Prop) (at level 0).
Local Notation "{ 'all2' P }" := (forall x y, P x y : Prop) (at level 0).
Local Notation "{ 'all3' P }" := (forall x y z, P x y z: Prop) (at level 0).
Local Notation ph := (phantom _).

Definition prop_near1 {X Y} (F : canonical_filter_on X Y) (x : X)
  (eq_x : x = canonical_filter_term F) P (phP : ph {all1 P}) :=
  (canonical_term_filter F) P.

Definition prop_near2 {X X' Y Y'} :=
 fun (F : canonical_filter_on X Y) (x : X) of x = canonical_filter_term F =>
 fun (F' : canonical_filter_on X' Y') (x' : X')
     of x' = canonical_filter_term F' =>
  fun P of ph {all2 P} =>
  (canonical_term_filter F) (fun x => canonical_term_filter F' (P x)).

End Near.

Notation "{ 'near' x , P }" :=
  (@prop_near1 _ _ _ x erefl _ (inPhantom P))
  (at level 0, format "{ 'near'  x ,  P }") : type_scope.
Notation "{ 'near' x & y , P }" :=
  (@prop_near2 _ _ _ _ _ x erefl _ y erefl _ (inPhantom P))
  (at level 0, format "{ 'near'  x  &  y ,  P }") : type_scope.

(** * Filters *)

(** ** Definitions *)

Class Filter {T : Type} (F : set (set T)) := {
  filterT : F setT ;
  filterI : forall P Q : set T, F P -> F Q -> F (P `&` Q) ;
  filterS : forall P Q : set T, P `<=` Q -> F P -> F Q
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

(* Near Tactic *)

Lemma filterP T (F : set (set T)) {FF : Filter F} (P : set T) :
  (exists2 Q : set T, F Q & forall x : T, Q x -> P x) <-> F P.
Proof.
split; last by exists P.
by move=> [Q FQ QP]; apply: (filterS QP).
Qed.

Definition extensible_property T (x : T) (P : Prop) := P.
Lemma extensible_propertyI T (x : T) (P : Prop) :
  P -> extensible_property x P.
Proof. by []. Qed.

Record in_filter T (F : set (set T)) := InFilter {
  prop_in_filter_proj : T -> Prop;
  prop_in_filterP_proj : F prop_in_filter_proj
}.

Module Type PropInFilterSig.
Axiom t : forall (T : Type) (F : set (set T)), in_filter F -> T -> Prop.
Axiom tE : t = prop_in_filter_proj.
End PropInFilterSig.
Module PropInFilter : PropInFilterSig.
Definition t := prop_in_filter_proj.
Lemma tE : t = prop_in_filter_proj. Proof. by []. Qed.
End PropInFilter.
Coercion PropInFilter.t : in_filter >-> Funclass.
Definition prop_in_filterE := PropInFilter.tE.

Lemma prop_in_filterP T F (iF : @in_filter T F) : F iF.
Proof. by rewrite prop_in_filterE; apply: prop_in_filterP_proj. Qed.

Ltac near x :=
apply/filterP;
let R := fresh "around" in
match goal with |- exists2 Q : set ?T, ?F Q & _ =>
  evar (R : set T);
  exists R; [rewrite /R {R}|move=> x /(extensible_propertyI x) ?]; last first
end.

Ltac have_near F x :=
match (type of [filter of F]) with set (set ?T) =>
  let R := fresh "around" in
  evar (R : set T);
  have [|x /(extensible_propertyI x) ?] := @filter_ex _ [filter of F] _ R;
  [rewrite /R {R}|]; last first
end.

Ltac assume_near x :=
match goal with Hx : extensible_property x _ |- _ =>
  eapply proj1; do 10?[by apply: Hx|eapply proj2] end.

Ltac end_near := do !
  [exact: prop_in_filterP|exact: filterT|by []|apply: filterI].

Ltac done :=
  trivial; hnf; intros; solve
   [ do ![solve [trivial | apply: sym_equal; trivial]
         | discriminate | contradiction | split]
   | case not_locked_false_eq_true; assumption
   | match goal with H : ~ _ |- _ => solve [case H; trivial] end
   | match goal with |- PropInFilter.t _ ?x => assume_near x end ].

Lemma near T (F : set (set T)) P (FP : F P) (x : T) : (InFilter FP) x -> P x.
Proof. by rewrite prop_in_filterE. Qed.
Arguments near {T F P} FP _ _.

Notation "[ 'valid_near' F ]" := (@InFilter _ F _ _) (format "[ 'valid_near'  F ]").
Definition valid_nearE := prop_in_filterE.

Lemma filter_forall {T : Type} {F} {FF: @Filter T F} (P : T -> Prop) :
  (forall x, P x) -> F P.
Proof. by move=> ?; apply/filterP; exists setT => //; apply: filterT. Qed.

Lemma filter_bind (T : Type) (F : set (set T)) :
  Filter F -> forall P Q : set T, {near F, P `<=` Q} -> F P -> F Q.
Proof.
move=> FF P Q subPQ FP; near x.
  by apply: (near subPQ) => //; assume_near x.
by end_near.
Qed.

Lemma filter_bind2 (T : Type) (F : set (set T)) :
  Filter F -> forall P Q R : set T, {near F, forall x, P x -> Q x -> R x} ->
  F P -> F Q -> F R.
Proof. by move=> ???? PQR FP; apply: filter_bind; apply: filter_bind FP. Qed.

Lemma filter_bind3 (T : Type) (F : set (set T)) :
  Filter F -> forall P Q R S : set T, {near F, forall x, P x -> Q x -> R x -> S x} ->
  F P -> F Q -> F R -> F S.
Proof. by move=> ????? PQR FP; apply: filter_bind2; apply: filter_bind FP. Qed.

Lemma filterS2 (T : Type) (F : set (set T)) :
  Filter F -> forall P Q R : set T, (forall x, P x -> Q x -> R x) ->
  F P -> F Q -> F R.
Proof. by move=> ???? /filter_forall; apply: filter_bind2. Qed.

Lemma filterS3 (T : Type) (F : set (set T)) :
  Filter F -> forall P Q R S : set T, (forall x, P x -> Q x -> R x -> S x) ->
  F P -> F Q -> F R -> F S.
Proof. by move=> ????? /filter_forall; apply: filter_bind3. Qed.

Lemma filter_const {T : Type} {F} {FF: @ProperFilter T F} (P : Prop) :
  F (fun=> P) -> P.
Proof. by move=> FP; case: (filter_ex FP). Qed.

Definition filter_from {I T : Type} (B : I -> set T) : set (set T) :=
  [set P | exists i, B i `<=` P].
Definition filter_from_base {T : Type} (B : set (set T)) : set (set T) :=
  [set P | exists2 b, B b & b `<=` P].

Lemma filter_from_family {I T : Type} (B : I -> set T) :
  filter_from_base [set of B] `<=>` filter_from B.
Proof.
split=> [P [b [i _ <- BiP]]|P [i BiP]]; first by exists i.
by exists (B i) => //; exists i.
Qed.

Lemma in_filter_from {I T : Type} (B : I -> set T) (i : I) :
   filter_from B (B i).
Proof. by exists i. Qed.

Lemma in_filter_from_base {T : Type} (B : set (set T)) b : B b ->
   filter_from_base B b.
Proof. by exists b. Qed.

Definition flim {T : Type} (F G : set (set T)) := G `<=` F.
Definition filter_le {T} := @flim T. (*compat*)
Notation "F `=>` G" := (flim F G)
  (at level 70, format "F  `=>`  G") : classical_set_scope.

Lemma flim_refl T (F : set (set T)) : F `=>` F.
Proof. exact. Qed.

Lemma flim_trans T (F G H : set (set T)) :
  (F `=>` G) -> (G `=>` H) -> (F `=>` H).
Proof. by move=> FG GH P /GH /FG. Qed.

Lemma filter_fromP {I T : Type} (B : I -> set T) (F : set (set T)) :
  Filter F ->
  F `=>` filter_from B <-> forall i, F (B i).
Proof.
split; first by move=> FB i; apply/FB/in_filter_from.
by move=> FB P [i BjP]; apply: (filterS BjP).
Qed.

Lemma filter_from_filter  {I T : Type} (B : I -> set T) :
  (exists _ : I, True) -> (forall i j, exists k, B k `<=` B i `&` B j) ->
  Filter (filter_from B).
Proof.
move=> [i0 _] Binter; constructor; first by exists i0.
- move=> P Q [i BiP] [j BjQ]; have [k BkPQ]:= Binter i j.
  by exists k => x /BkPQ [/BiP ? /BjQ].
- by move=> P Q subPQ [i BiP]; exists i; apply: subset_trans subPQ.
Qed.

Lemma filter_from_baseP {T : Type} (B : set (set T)) (F : set (set T)) :
  Filter F ->
  F `=>` filter_from_base B <-> forall b, B b -> F b.
Proof.
split; first by move=> FB b Bb; apply/FB/in_filter_from_base.
by move=> FB P [b Bb bP]; apply: (filterS bP); apply: FB.
Qed.

Lemma filter_from_base_filter {T : Type} (B : set (set T)) :
  (exists b, B b) ->
  (forall b1 b2, B b1 -> B b2 -> exists2 b, B b & b `<=` b1 `&` b2) ->
  Filter (filter_from_base B).
Proof.
move=> [b0 Bb0] Binter; constructor; first by exists b0.
  move=> P Q [b1 Bb1 b1P] [b2 Bb2 b2Q]; have [||b Bb b_sub] // := Binter b1 b2.
  by exists b => // R /b_sub [/b1P PR /b2Q QR].
by move=> P Q subPQ [b Bb bP]; exists b; apply: subset_trans subPQ.
Qed.

(** ** Limits expressed with filters *)

Notation "F --> G" := (flim [filter of F] [filter of G])
  (at level 70, format "F  -->  G") : classical_set_scope.

Lemma filter_le_refl T (F : set (set T)) : F --> F. (*compat*)
Proof. exact. Qed.

Lemma filter_le_trans T (F G H : set (set T)) : (*compat*)
  (F --> G) -> (G --> H) -> (F --> H).
Proof. exact: flim_trans. Qed.

Definition filtermap {T U : Type} (f : T -> U) (F : set (set T)) :=
  [set P | F (f @^-1` P)].
Arguments filtermap _ _ _ _ _ /.

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
- exact: filterT.
- exact: filterI.
- by apply: filterS=> ?/PQ.
Qed.

Global Instance filtermap_proper_filter T U (f : T -> U) (F : set (set T)) :
  ProperFilter F -> ProperFilter (f @ F).
Proof.
move=> FF; apply: Build_ProperFilter';
by rewrite filtermapE; apply: filter_not_empty.
Qed.
Definition filtermap_proper_filter' := filtermap_proper_filter.

Definition filtermapi {T U : Type} (f : T -> set U) (F : set (set T)) :=
  [set P | {near F, forall x, exists y, f x y /\ P y}].

Notation "E `@[ x --> F ]" := (filtermapi (fun x => E) [filter of F])
  (at level 60, x ident, format "E  `@[ x  -->  F ]") : classical_set_scope.
Notation "f `@ F" := (filtermapi f [filter of F])
  (at level 60, format "f  `@  F") : classical_set_scope.

Lemma filtermapiE {U V : Type} (f : U -> set V)
  (F : set (set U)) (P : set V) :
  filtermapi f F P = {near F, forall x, exists y, f x y /\ P y}.
Proof. by []. Qed.

Global Instance filtermapi_filter T U (f : T -> U -> Prop) (F : set (set T)) :
  infer {near F, is_totalfun f} -> Filter F -> Filter (f `@ F).
Proof.
move=> f_totalfun FF; rewrite /filtermapi; apply: Build_Filter. (* bug *)
- by apply: filterS f_totalfun => x [[y Hy] H]; exists y.
- move=> P Q FP FQ; near x.
    have [//|y [fxy Py]] := near FP x.
    have [//|z [fxz Qz]] := near FQ x.
    have [//|_ fx_prop] := near f_totalfun x.
    by exists y; split => //; split => //; rewrite [y](fx_prop _ z).
  by end_near.
- move=> P Q subPQ FP; near x.
    by have [//|y [fxy /subPQ Qy]] := near FP x; exists y.
  by end_near.
Qed.

Global Instance filtermapi_proper_filter
  T U (f : T -> U -> Prop) (F : set (set T)) :
  infer {near F, is_totalfun f} ->
  ProperFilter F -> ProperFilter (f `@ F).
Proof.
move=> f_totalfun FF; apply: Build_ProperFilter.
by move=> P; rewrite /filtermapi => /filter_ex [x [y [??]]]; exists y.
Qed.
Definition filter_map_proper_filter' := filtermapi_proper_filter.

Lemma flim_id T (F : set (set T)) : x @[x --> F] --> F.
Proof. exact. Qed.
Arguments flim_id {T F}.

Lemma filterlim_id T (F : set (set T)) : x @[x --> F] --> F. (*compat*)
Proof. exact. Qed.

Lemma appfilter U V (f : U -> V) (F : set (set U)) :
  f @ F = [set P : _ -> Prop | {near F, forall x, P (f x)}].
Proof. by []. Qed.

Lemma flim_app U V (F G : set (set U)) (f : U -> V) :
  F --> G -> f @ F --> f @ G.
Proof. by move=> FG P /=; exact: FG. Qed.
Lemma filterlim_app U V (F G : set (set U)) (f : U -> V) : (*compat*)
  F --> G -> f @ F --> f @ G.
Proof. by move=> FG P /=; exact: FG. Qed.

Lemma flimi_app U V (F G : set (set U)) (f : U -> set V) :
  F --> G -> f `@ F --> f `@ G.
Proof. by move=> FG P /=; exact: FG. Qed.

Lemma filter_comp T U V (f : T -> U) (g : U -> V) (F : set (set T)) : (*compat*)
  g \o f @ F = g @ (f @ F).
Proof. by []. Qed.

Lemma flim_comp T U V (f : T -> U) (g : U -> V)
  (F : set (set T)) (G : set (set U)) (H : set (set V)) :
  f @ F `=>` G -> g @ G `=>` H -> g \o f @ F `=>` H.
Proof. by move=> fFG gGH; apply: filter_le_trans gGH => P /fFG. Qed.

Lemma flimi_comp T U V (f : T -> U) (g : U -> set V)
  (F : set (set T)) (G : set (set U)) (H : set (set V)) :
  f @ F `=>` G -> g `@ G `=>` H -> g \o f `@ F `=>` H.
Proof. by move=> fFG gGH; apply: filter_le_trans gGH => P /fFG. Qed.

Lemma filterlim_comp T U V (f : T -> U) (g : U -> V)
  (F : set (set T)) (G : set (set U)) (H : set (set V)) : (*compat*)
  f @ F `=>` G -> g @ G `=>` H -> g \o f @ F `=>` H.
Proof. exact: flim_comp. Qed.

Lemma flim_eq_loc {T U} {F : set (set T)} {FF : Filter F} (f g : T -> U) :
  {near F, f =1 g} -> g @ F `=>` f @ F.
Proof. by move=> eq_fg P /=; apply: filterS2 eq_fg => x <-. Qed.

Lemma flimi_eq_loc {T U} {F : set (set T)} {FF : Filter F} (f g : T -> set U) :
  {near F, f =2 g} -> g `@ F `=>` f `@ F.
Proof.
move=> eq_fg P /=; apply: filterS2 eq_fg => x eq_fg [y [fxy Py]].
by exists y; rewrite -eq_fg.
Qed.

Lemma filterlim_eq_loc {T U} {F : set (set T)}
  {FF : Filter F} (f g : T -> U) : (*compat*)
  {near F, f =1 g} -> g @ F `=>` f @ F.
Proof. exact: flim_eq_loc. Qed.

Lemma filterlim_ext_loc {T U} {F : set (set T)} {G : set (set U)}
  {FF : Filter F} (f g : T -> U) : (*compat*)
  {near F, f =1 g} -> f @ F `=>` G -> g @ F `=>` G.
Proof. by move=> /flim_eq_loc/flim_trans; apply. Qed.

Lemma filterlim_ext {T U} {F : set (set T)} {G : set (set U)}
  {FF : Filter F} (f g : T -> U) : (*compat*)
  (forall x, f x = g x) -> f @ F --> G -> g @ F --> G.
Proof. by move=> /(@filter_forall _ F) /filterlim_ext_loc; apply. Qed.

Lemma filterlim_trans {T} {F G H : set (set T)} : F --> G -> G --> H -> F --> H.
Proof. exact: flim_trans. Qed.

Lemma filterlim_filter_le_1 {T U} {F G : set (set T)} {H : set (set U)}
  (f : T -> U) : G --> F -> f @ F --> H -> f @ G --> H. (*compat*)
Proof. by move=> /filterlim_app /filter_le_trans; apply. Qed.

Lemma filterlim_filter_le_2 {T U} {F : set (set T)} {G H : set (set U)}
  (f : T -> U) : G --> H -> f @ F --> G -> f @ F --> H. (*compat*)
Proof. by move=> GH ?; apply: filter_le_trans GH. Qed.

Lemma filterlimi_comp T U V (f : T -> U) (g : U -> set V)
  (F : set (set T)) (G : set (set U)) (H : set (set V)) :
  f @ F --> G -> g `@ G --> H -> g (f x) `@[x --> F] --> H. (*compat*)
Proof. exact: flimi_comp. Qed.

Lemma filterlimi_ext_loc {T U} {F : set (set T)} {G : set (set U)}
  {FF : Filter F} (f g : T -> set U) :
  {near F, forall x y, f x y <-> g x y} ->
  f `@ F --> G -> g `@ F --> G. (* compat *)
Proof.
move=> eq_fg; apply: flim_trans => P /=; apply flimi_eq_loc.
by apply: filterS eq_fg => Q eq_fg y; rewrite propeqE.
Qed.

Lemma filterlimi_ext  {T U} {F : set (set T)} {G : set (set U)}
  {FF : Filter F} (f g : T -> set U) :
  (forall x y, f x y <-> g x y) ->
  f `@ F --> G -> g `@ F --> G.
Proof. by move=> /filter_forall; apply: filterlimi_ext_loc. Qed.

Lemma filterlimi_filter_le_1 {T U} {F G : set (set T)} {H : set (set U)}
  (f : T -> set U) : G --> F -> f `@ F --> H -> f `@ G --> H. (* compat *)
Proof. by move=> /flimi_app /flim_trans GF /GF. Qed.

Lemma filterlimi_filter_le_2  {T U} {F : set (set T)} {G H : set (set U)}
  (f : T -> set U) : G --> H -> f `@ F --> G -> f `@ F --> H. (* compat *)
Proof. by move=> /(flim_trans _) GH /GH. Qed.

(** ** Specific filters *)

(** Filters for pairs *)

Definition filter_prod {T U : Type}
  (F : set (set T)) (G : set (set U)) : set (set (T * U)) :=
  filter_from_base [set P `*` Q | P in F & Q in G].

Definition apply_filter_prod {X1 X2 Y1 Y2} (f : Y1 -> set (set X1))
  (g : Y2 -> set (set X2)) (y1 : Y1) (y2 : Y2) : set (set (X1 * X2)) :=
  filter_prod (f y1) (g y2).
Arguments apply_filter_prod /.

Canonical canonical_filter_prod X1 X2 (Z1 : canonical_filter X1)
  (Z2 : canonical_filter X2) : canonical_filter (X1 * X2) :=
  @CanonicalFilter _ _ (fun x => apply_filter_prod
  (@canonical_type_filter _ Z1) (@canonical_type_filter _ Z2) x.1 x.2).

Global Instance filter_prod_filter  T U (F : set (set T)) (G : set (set U)) :
  Filter F -> Filter G -> Filter (filter_prod F G).
Proof.
move=> FF FG; apply: filter_from_base_filter.
  by exists (setT `*` setT); do 2?exists setT =>//; apply: filterT.
move=> _ _ [P FP [Q FQ <-]] [P' FP' [Q' FQ' <-]].
exists ((P `&` P') `*` (Q `&` Q')); first by do?eexists; apply: filterI.
by move=> [x y] [/= [??] [??]]; do !split.
Qed.

Global Instance filter_prod_proper {T1 T2 : Type}
  {F : (T1 -> Prop) -> Prop} {G : (T2 -> Prop) -> Prop}
  {FF : ProperFilter F} {FG : ProperFilter G} :
  ProperFilter (filter_prod F G).
Proof.
apply: Build_ProperFilter'; rewrite /filter_prod=> - [_ [P FP [Q GQ <-]]].
move=> PQsub0; suff Psub0: P `<=` set0.
  by apply: (filter_not_empty F); apply: filterS FP.
move=> x Px; suff Qsub0: Q `<=` set0.
  by apply: (filter_not_empty G); apply: filterS GQ.
by move=> y Qy; apply: (PQsub0 (x, y)); do ?eexists.
Qed.
Definition filter_prod_proper' := @filter_prod_proper.

Lemma filter_prod1 {T U} {F : set (set T)} {G : set (set U)}
  {FG : Filter G} (P : set T) :
  {near F, forall x, P x} -> {near (F, G), forall x, P x.1}.
Proof.
move=> FP; exists (P `*` setT); last by move=> ? [].
by do ![eexists]=> //; apply: filterT.
Qed.

Lemma filter_prod2 {T U} {F : set (set T)} {G : set (set U)}
  {FF : Filter F} (P : set U) :
  {near G, forall x, P x} -> {near (F, G), forall x, P x.2}.
Proof.
move=> GP; exists (setT `*` P); last by move=> ? [].
by do ![eexists]=> //; apply: filterT.
Qed.

Lemma flim_fst {T U F G} {FG : Filter G} :
  (@fst T U) @ filter_prod F G --> F.
Proof. by move=> P; apply: filter_prod1. Qed.

Lemma flim_snd {T U F G} {FF : Filter F} :
  (@snd T U) @ filter_prod F G --> G.
Proof. by move=> P; apply: filter_prod2. Qed.

Lemma extensible_propertyE (T : Type) (x : T) (P : Prop) :
  extensible_property x P -> P.
Proof. by []. Qed.
Arguments extensible_propertyE {T} x {P}.

Lemma filterlim_pair {T U V F} {G : set (set U)} {H : set (set V)}
  {FF : Filter F} {FG : Filter G} {FH : Filter H} (f : T -> U) (g : T -> V) :
  f @ F --> G -> g @ F --> H ->
  (f x, g x) @[x --> F] --> (G, H).
Proof.
move=> fFG gFH P /= [_ [A GA [B GB <-]] subP]; near x.
  by apply: subP; split=> /=; assume_near x.
by end_near; [apply: fFG|apply: gFH].
Qed.

Lemma flim_comp2 {T U V W}
  {F : set (set T)} {G : set (set U)} {H : set (set V)} {I : set (set W)}
  {FF : Filter F} {FG : Filter G} {FH : Filter H}
  (f : T -> U) (g : T -> V) (h : U -> V -> W) :
  f @ F --> G -> g @ F --> H ->
  h (fst x) (snd x) @[x --> (G, H)] --> I ->
  h (f x) (g x) @[x --> F] --> I.
Proof. by move=> fFG gFH hGHI P /= IP; apply: filterlim_pair (hGHI _ IP). Qed.
Arguments flim_comp2 {T U V W F G H I FF FG FH f g h} _ _ _.
Definition filterlim_comp_2 := @flim_comp2.

(* Lemma filterlimi_comp_2 {T U V W} *)
(*   {F : set (set T)} {G : set (set U)} {H : set (set V)} {I : set (set W)} *)
(*   {FF : Filter F} *)
(*   (f : T -> U) (g : T -> V) (h : U -> V -> set W) : *)
(*   f @ F --> G -> g @ F --> H -> *)
(*   h (fst x) (snd x) `@[x --> (G, H)] --> I -> *)
(*   h (f x) (g x) `@[x --> F] --> I. *)
(* Proof. *)
(* intros Cf Cg Ch. *)
(* change (fun x => h (f x) (g x)) with (fun x => h (fst (f x, g x)) (snd (f x, g x))). *)
(* apply: filterlimi_comp Ch. *)
(* now apply filterlim_pair. *)
(* Qed. *)

(** Restriction of a filter to a domain *)

Definition within {T : Type} (D : set T) (F : set (set T)) (P : set T) :=
  {near F, D `<=` P}.

Global Instance within_filter T D F : Filter F -> Filter (@within T D F).
Proof.
move=> FF; rewrite /within; constructor.
- by apply: filter_forall.
- by move=> P Q; apply: filterS2 => x DP DQ Dx; split; [apply: DP|apply: DQ].
- by move=> P Q subPQ; apply: filterS => x DP /DP /subPQ.
Qed.

Lemma filter_le_within {T} {F : set (set T)} {FF : Filter F} D :
  within D F --> F.
Proof. by move=> P; apply: filterS. Qed.

Lemma filterlim_within_ext {T U F} {G : set (set U)}
  {FF : Filter F} (D : set T) (f g : T -> U) :
  (forall x, D x -> f x = g x) ->
  f @ within D F --> G ->
  g @ within D F --> G.
Proof.
move=> eq_fg; apply: filter_le_trans; apply: filterlim_eq_loc.
by rewrite /within /prop_near1 /=; apply: filter_forall.
Qed.

Definition subset_filter {T} (F : set (set T)) (D : set T) :=
  [set P : set {x | D x} | F [set x | forall Dx : D x, P (exist _ x Dx)]].
Arguments subset_filter {T} F D _.

Global Instance subset_filter_filter T F (D : set T) :
  Filter F -> Filter (subset_filter F D).
Proof.
move=> FF; constructor; rewrite /subset_filter.
- exact: filter_forall.
- by move=> P Q; apply: filterS2 => x PD QD Dx; split.
- by move=> P Q subPQ; apply: filterS => R PD Dx; apply: subPQ.
Qed.

Lemma subset_filter_proper {T F} {FF : Filter F} (D : set T) :
  (forall P, F P -> ~ ~ exists x, D x /\ P x) ->
  ProperFilter (subset_filter F D).
Proof.
move=> DAP; apply: Build_ProperFilter'; rewrite /subset_filter => subFD.
by have /(_ subFD) := DAP (~` D); apply => -[x [dx /(_ dx)]].
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
Definition locally {M : uniformType} (x : M) : set (set M) :=
  @filter_from posreal _ (ball x).
Definition uniformType_is_canonical_filter {M : uniformType} :=
   @CanonicalFilter M M locally.
Coercion uniformType_is_canonical_filter : uniformType >-> canonical_filter.
Canonical uniformType_is_canonical_filter.

Section UniformGet.

Context {T : uniformType}.
Definition get : set T -> T := xget point.

Lemma getPex (P : set T) : (exists x, P x) -> P (get P).
Proof. exact: (xgetPex point). Qed.

Lemma getP (P : set T) (x : T): P x -> P (get P).
Proof. exact: (xgetP point). Qed.

Lemma get_prop (P : set T) (x : T) : P x -> is_prop P -> get P = x.
Proof. exact: (xget_prop point). Qed.

Lemma get_unique (P : set T) (x : T) :
   P x -> (forall y, P y -> y = x) -> get P = x.
Proof. exact: (xget_unique point). Qed.
Definition iota_unique := @get_unique.

Lemma getPN (P : set T) : (forall x, ~ P x) -> get P = point.
Proof. exact: (xgetPN point). Qed.

Definition lim (F : set (set T)) : T := get [set x | F --> x].

(* Definition lim_in {M : uniformType} (F : set (set M)) T : T := *)
(*    get (fun x : T => F --> x). *)
(* Notation "[ 'lim' F 'in' T ]" := (lim_in F T). *)
(* Definition type_of_filter {M : uniformType} (F : set (set M)) := M. *)
(* Notation lim F := [lim F in type_of_filter F]. *)

End UniformGet.

(* Unique Choice for compatilibility reasons *)
Notation iota := get.

Module AbsRing.

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
Hint Resolve absr_ge0.

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

Reserved Notation  "`|[ x ]|" (at level 0, x at level 99, format "`|[ x ]|").

Program Definition R_AbsRingMixin :=
 @AbsRing.Mixin _ normr (normr0 _) (normrN1 _) (@ler_norm_add _) _ (@normr0_eq0 _).
Next Obligation. by rewrite normrM. Qed.
Canonical R_absRingType := AbsRingType R R_AbsRingMixin.

Definition R_UniformSpace_mixin := @AbsRingUniformMixin R_absRingType.
Canonical R_UniformSpace := UniformType R R_UniformSpace_mixin.
Canonical R_canonical_filter := @CanonicalFilter R R locally.
Canonical Ro_UniformSpace := UniformType R^o R_UniformSpace_mixin.
Canonical Ro_canonical_filter := @CanonicalFilter R R^o locally.

Section uniformType1.
Context {M : uniformType}.

Lemma ball_center (x : M) (e : posreal) : ball x e x.
Proof. exact: Uniform.ax1. Qed.
Hint Resolve ball_center.

Lemma ballxx (x : M) (e : R) : (0 < e)%R -> ball x e x.
Proof. by move=> e_gt0; apply: ball_center (PosReal e_gt0). Qed.

Lemma ball_sym (x y : M) (e : R) : ball x e y -> ball y e x.
Proof. exact: Uniform.ax2. Qed.

Lemma ball_triangle (y x z : M) (e1 e2 : R) :
  ball x e1 y -> ball y e2 z -> ball x (e1 + e2) z.
Proof. exact: Uniform.ax3. Qed.

Lemma ball_split (z x y : M) (e : R) :
  ball x (e / 2) z -> ball z (e / 2) y -> ball x e y.
Proof. by move=> /ball_triangle h /h; rewrite -double_var. Qed.

Lemma ball_splitr (z x y : M) (e : R) :
  ball z (e / 2) x -> ball z (e / 2) y -> ball x e y.
Proof. by move=> /ball_sym /ball_split; apply. Qed.

Lemma ball_splitl (z x y : M) (e : R) :
  ball x (e / 2) z -> ball y (e / 2) z -> ball x e y.
Proof. by move=> bxz /ball_sym /(ball_split bxz). Qed.

Lemma ball_ler (x : M) (e1 e2 : R) : e1 <= e2 -> ball x e1 `<=` ball x e2.
Proof.
move=> le12 y; case: ltrgtP le12 => [//|lte12 _|->//].
by rewrite -[e2](subrK e1); apply/ball_triangle/ballxx; rewrite subr_gt0.
Qed.

Lemma ball_le (x : M) (e1 e2 : R) : (e1 <= e2)%coqR -> ball x e1 `<=` ball x e2.
Proof. by move=> /RleP/ball_ler. Qed.

Definition close (x y : M) : Prop := forall eps : posreal, ball x eps y.

Lemma close_refl (x : M) : close x x. Proof. by []. Qed.

Lemma close_sym (x y : M) : close x y -> close y x.
Proof. by move=> ??; apply: ball_sym. Qed.

Lemma close_trans (x y z : M) : close x y -> close y z -> close x z.
Proof. by move=> ?? eps; apply: ball_split. Qed.

Lemma close_limxx (x y : M) : close x y -> x --> y.
Proof.
move=> cxy P /= [eps epsP]; exists [posreal of eps / 2] => z bxz.
by apply: epsP; apply: ball_splitr (cxy _) bxz.
Qed.

End uniformType1.

Hint Resolve ball_center.
Hint Resolve close_refl.

(** ** Specific uniform spaces *)

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
  @Uniform.Mixin (U * V) prod_point _ prod_ball_center
                 prod_ball_sym prod_ball_triangle.

Canonical prod_uniformType (U V : uniformType) :=
  UniformType (U * V) (prod_uniformType_mixin U V).

(** Functional metric spaces *)

Section fct_Uniform.

Variable (T : choiceType) (U : uniformType).

Definition fct_point : T -> U := fun=> point.

Definition fct_ball (x : T -> U) (eps : R) (y : T -> U) :=
  forall t : T, ball (x t) eps (y t).

Lemma fct_ball_center (x : T -> U) (e : posreal) : fct_ball x e x.
Proof. by move=> t; apply: ball_center. Qed.

Lemma fct_ball_sym (x y : T -> U) (e : R) : fct_ball x e y -> fct_ball y e x.
Proof. by move=> P t; apply: ball_sym. Qed.

Lemma fct_ball_triangle (x y z : T -> U) (e1 e2 : R) :
  fct_ball x e1 y -> fct_ball y e2 z -> fct_ball x (e1 + e2) z.
Proof. by move=> xy yz t; apply: (@ball_triangle _ (y t)). Qed.

Definition fct_uniformType_mixin :=
  @Uniform.Mixin _ fct_point _ fct_ball_center fct_ball_sym fct_ball_triangle.

Canonical fct_uniformType := UniformType (T -> U) fct_uniformType_mixin.
Canonical generic_source_filter := @CanonicalFilterSource _ _ _ locally.

End fct_Uniform.

(** ** Local predicates *)
(** locally_dist *)

Definition locally_dist {T : Type} (d : T -> R) :=
  filter_from (fun delta : posreal => [set y | (d y < delta)%R]).

Global Instance locally_dist_filter T (d : T -> R) : Filter (locally_dist d).
Proof.
apply: filter_from_filter; first by exists [posreal of 1].
move=> e1 e2; exists [posreal of minr (e1 : R) (e2 : R)].
by move=> P /=; rewrite ltr_minr => /andP [dPe1 dPe2].
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
apply: filter_from_filter; first by exists [posreal of 1].
move=> e1 e2; exists [posreal of minr (e1 : R) (e2 : R)].
by move=> P /= xP; split; apply: ball_ler xP; rewrite ler_minl lerr ?orbT.
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
  locally x P -> locally x (locally^~ P).
Proof.
move=> [dp Hp].
exists [posreal of dp / 2] => y xy.
exists [posreal of dp / 2] => z yz.
by apply: Hp; apply: ball_split yz.
Qed.

Lemma locally_singleton (x : T) (P : T -> Prop) : locally x P -> P x.
Proof. move=> [dp H]; by apply/H/ball_center. Qed.

Lemma locally_ball (x : T) (eps : posreal) : locally x (ball x eps).
Proof. by exists eps. Qed.
Hint Resolve locally_ball.

Lemma forallN {U} (P : set U) : (forall x, ~ P x) = ~ exists x, P x.
Proof. (*boolP*)
rewrite propeqE; split; first by move=> fP [x /fP].
by move=> nexP x Px; apply: nexP; exists x.
Qed.

Lemma NNP (P : Prop) : (~ ~ P) <-> P. (*boolP*)
Proof. by split=> [nnp|p /(_ p)//]; have [//|/nnp] := asboolP P. Qed.

Lemma eqNNP (P : Prop) : (~ ~ P) = P. (*boolP*)
Proof. by rewrite propeqE NNP. Qed.

Lemma existsN {U} (P : set U) : (exists x, ~ P x) = ~ forall x, P x. (*boolP*)
Proof.
rewrite propeqE; split=> [[x Px] Nall|Nall]; first by apply: Px.
by apply/NNP; rewrite -forallN => allP; apply: Nall => x; apply/NNP.
Qed.

Lemma ex_ball_sig (x : T) (P : set T) :
  ~ (forall eps : posreal, ~ (ball x eps `<=` ~` P)) ->
    {d : posreal | ball x d `<=` ~` P}.
Proof.
rewrite forallN eqNNP => exNP.
pose D := [set d : R | d > 0 /\ ball x d `<=` ~` P].
have [|d_gt0] := @getPex _ D; last by exists (PosReal d_gt0). 
by move: exNP => [e eP]; exists (e : R).
Qed.
Definition locally_not' := ex_ball_sig. (*compat*)

Lemma locallyN (x : T) (P : set T) :
  ~ (forall eps : posreal, ~ (ball x eps `<=` ~` P)) ->
  locally x (~` P).
Proof. by move=> /ex_ball_sig [e]; exists e. Qed.
Definition locally_not := @locallyN. (*compat*)

Lemma locallyN_ball (x : T) (P : set T) :
  locally x (~` P) -> {d : posreal | ball x d `<=` ~` P}.
Proof. by move=> xNP; apply: ex_ball_sig; have [e eP /(_ _ eP)] := xNP. Qed.

Lemma locally_ex (x : T) (P : T -> Prop) : locally x P ->
  {d : posreal | forall y, ball x d y -> P y}.
Proof.
move=> xP; pose D := [set d : R | d > 0 /\ forall y, ball x d y -> P y].
have [|d_gt0 dP] := @getPex _ D; last by exists (PosReal d_gt0).
by move: xP => [e bP]; exists (e : R).
Qed.

Lemma flim_close {F} {FF : ProperFilter F} (x y : T) :
  F --> x -> F --> y -> close x y.
Proof.
move=> Fx Fy e; have_near F z; [by apply: (@ball_splitl _ z); assume_near z|].
by end_near; [apply/Fx/locally_ball|apply/Fy/locally_ball].
Qed.
Definition is_filter_lim_close := @flim_close. (*compat*)

Lemma flimx_close (x y : T) : x --> y -> close x y.
Proof. exact: flim_close. Qed.
Definition is_filter_lim_locally_close := @flimx_close.  (*compat*)

End Locally.
Hint Resolve locally_ball.

Definition cvg (U : Type) (T : canonical_filter U) :=
  fun (T' : Type) & canonical_filter_type T = T' =>
  fun F : set (set U) => exists l : T, F --> l.

Notation "[ 'cvg' F 'in' T ]" :=
  (@cvg _ _ T erefl [filter of F])
  (format "[ 'cvg'  F  'in'  T ]") : classical_set_scope.
Notation continuous f := (forall x, f%function @ locally x --> f%function x).

Lemma flim_const {T} {U : uniformType} {F : set (set T)}
   {FF : Filter F} (a : U) : a @[_ --> F] --> a.
Proof.
move=> P [eps HP]; rewrite appfilter /=.
by apply: filter_forall=> ?; apply/HP/ball_center.
Qed.
Arguments flim_const {T U F FF} a.

Lemma filterlim_const {T} {U : uniformType} {F : set (set T)} (*compat*)
   {FF : Filter F} (a : U) : a @[_ --> F] --> a.
Proof. exact: flim_const. Qed.

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

Lemma cvgP (F : set (set U)) : cvg_spec F (lim F) [cvg F in U].
Proof.
have [cvg|dvg] := pselect [cvg F in U].
  by rewrite (propT cvg); apply: HasLim; rewrite -cvgE.
by rewrite (propF dvg) (dvgP _) //; apply: HasNoLim.
Qed.

Lemma cvgI (F : set (set U)) (l : U) : F --> l -> [cvg F in U].
Proof. by exists l. Qed.

Lemma close_lim (F1 F2 : set (set U)) {FF2 : ProperFilter F2} :
  F1 --> F2 -> F2 --> F1 -> close (lim F1) (lim F2).
Proof.
have [l F1l _|dvgF1]:= cvgP F1.
  move=> /filter_le_trans /(_ F1l) F2l.
  apply: (@flim_close _ F2) => //.
  by rewrite -cvgE; exists l.
have [l F2l|//]:= cvgP F2.
move=> /filter_le_trans /(_ F2l) F1l _.
by have := dvgF1 (ex_intro _ l F1l).
Qed.

Lemma filterlim_closeP (F : set (set U)) (l : U) :
  ProperFilter F ->
  F --> l <-> ([cvg F in U] /\ close (lim F) l).
Proof.
rewrite cvgE; split=> [Fl|[FlF cl]].
  have FlF: F --> lim F by rewrite -cvgE; exists l.
  by split=> //; apply: flim_close.
by apply: filter_le_trans (close_limxx cl).
Qed.

End Cvg.
Arguments close_lim {U} F1 F2 {FF2} _.

Section Locally_fct.

Context {T : Type} {U : uniformType}.

Lemma flim_ballP {F} {FF : Filter F} (y : U) :
  F --> y <-> forall eps : posreal, F [set x | ball y eps x].
Proof. exact: filter_fromP. Qed.
Definition filterlim_locally := @flim_ballP.

Lemma flim_ball {F} {FF : Filter F} (y : U) :
  F --> y -> forall eps : posreal, F [set x | ball y eps x].
Proof. by move/flim_ballP. Qed.

Lemma app_filterlim_locally {F} {FF : Filter F} (f : T -> U) y :
  f @ F --> y <-> forall eps : posreal, F [set x | ball y eps (f x)].
Proof. exact: flim_ballP. Qed.

Lemma flimi_ballP {F} {FF : Filter F} (f : T -> U -> Prop) y :
  f `@ F --> y <->
  forall eps : posreal, F [set x | exists z, f x z /\ ball y eps z].
Proof.
split=> [Fy eps|Fy P [eps subP]]; first exact/Fy/locally_ball.
rewrite /filtermapi /=; near x.
  have [//|z [fxz yz]] := near (Fy eps) x.
  by exists z => //; split => //; apply: subP.
by end_near.
Qed.
Definition filterlimi_locally := @flimi_ballP.

Lemma flimi_ball {F} {FF : Filter F} (f : T -> U -> Prop) y :
  f `@ F --> y ->
  forall eps : posreal, F [set x | exists z, f x z /\ ball y eps z].
Proof. by move/flimi_ballP. Qed.

(* :TODO: remove *)
Lemma filterlim_locally_close {F} {FF: ProperFilter F} (f : T -> U) (l l' : U) :
  f @ F --> l -> f @ F --> l' -> close l l'.
Proof. exact: is_filter_lim_close. Qed.

(* :TODO: refactor *)
Lemma flimi_close {F} {FF: ProperFilter F} (f : T -> set U) (l l' : U) :
  {near F, is_fun f} -> f `@ F --> l -> f `@ F --> l' -> close l l'.
Proof.
move=> f_prop fFl fFl'.
suff f_totalfun: infer {near F, is_totalfun f} by exact: flim_close fFl fFl'.
near x => /=.
  split; last exact: (near f_prop).
  by have [//|y [fxy _]] := near (flimi_ball fFl [posreal of 1]) x; exists y.
by end_near.
Qed.
Definition filterlimi_locally_close := @flimi_close.

End Locally_fct.

Lemma is_filter_lim_filtermap {T: uniformType} {U : uniformType}
  (F : set (set T)) x (f : T -> U) :
   {for x, continuous f} -> F --> x -> f @ F --> f x.
Proof. by move=> cf fx P /cf /fx. Qed.

(** locally' *)

(* Should have a generic ^' operator *)
Definition locally' {T : uniformType} (x : T) :=
  within (fun y => y <> x) (locally x).

Global Instance locally'_filter {T : uniformType} (x : T) :
  Filter (locally' x).
Proof. exact: within_filter. Qed.

Section at_point.

Context {T : uniformType}.

Definition at_point (a : T) (P : set T) : Prop := P a.

Global Instance at_point_filter (a : T) : ProperFilter (at_point a).
Proof. by constructor=> //; constructor=> // P Q subPQ /subPQ. Qed.

End at_point.

(** ** Topology in uniform spaces *)

Section Open.

Context {T : uniformType}.

Notation "D ^o" := (locally^~ D).
Definition open (D : set T) := D `<=` D^o.

Lemma openP (D E : set T) : open D -> (D `<=` E) -> (D `<=` E^o).
Proof.
move=> D_open DE x Dx; near y; first by apply: DE; assume_near y.
by end_near; apply: D_open.
Qed.
Definition locally_open := @openP.

Lemma open_ext (D E : set T) : (D `<=>` E) -> open D -> open E.
Proof.
move=> DE D_open x Ex; near y; first by apply DE; assume_near y.
by end_near; apply: D_open; apply DE.
Qed.

Lemma openI (D E : set T) : open D -> open E -> open (D `&` E).
Proof.
move=> D_open E_open x [Dx Ex]; near y; first by split; assume_near y.
by end_near; [apply: D_open|apply E_open].
Qed.

Lemma open_bigU {I : Type} (D : I -> set T) :
  (forall i, open (D i)) -> open (\bigcup_i D i).
Proof.
move=> D_open x [i _ Dix]; near y; first by exists i => //; assume_near y.
by end_near; apply: D_open.
Qed.

Lemma openU (D E : set T) : open D -> open E -> open (D `|` E).
Proof.
move=> D_open E_open x [Dx|Ex].
- by move/filterS : (D_open x Dx); apply; left.
- by move/filterS : (E_open x Ex); apply; right.
Qed.

Lemma openT : open setT. Proof. by move=> *; apply: filterT. Qed.
Lemma open0 : open set0. Proof. by []. Qed.

End Open.

Lemma open_comp  {T U : uniformType} (f : T -> U) (D : set U) :
  {in f @^-1` D, continuous f} -> open D -> open (f @^-1` D).
Proof.
move=> f_continous open_D x /= Dfx.
apply: f_continous => //=; first by rewrite in_setE.
exact: open_D.
Qed.

(** ** Closed sets in uniform spaces *)

Section Closed.

Context {T : uniformType}.

Definition closed (D : set T) :=
  forall x, ~ {near x, forall x, ~ D x} -> D x.

Lemma openN (D : set T) : closed D -> open (~` D).
Proof.
move=> D_close x Dx; apply: locallyN => subD.
by apply/Dx/D_close => -[eps /subD].
Qed.

Lemma closedN (D : set T) : open D -> closed (~` D).
Proof.
move=> D_open x /= Lx Dx; apply: Lx.
by apply: filterS (D_open _ Dx) => y Dy /(_ Dy).
Qed.

Lemma closed_ext (D E : set T) : (forall x, D x <-> E x) ->
  closed D -> closed E.
Proof.
move=> DE D_closed x Ex; apply/DE/D_closed => Dx; apply: Ex.
by apply: filterS Dx => y /DE.
Qed.

Lemma closed_bigI {I} (D : I -> set T) :
  (forall i, closed (D i)) -> closed (\bigcap_i D i).
Proof.
move=> D_closed x Dx i _; apply/D_closed=> Dix; apply: Dx.
by apply: filterS Dix => y NDiy /(_ i _) /NDiy; apply.
Qed.

Lemma closedI (D E : set T) : closed D -> closed E -> closed (D `&` E).
Proof.
move=> D_closed E_closed x DEx; split.
  by apply/D_closed=> Dx; apply: DEx; apply: filterS Dx=> y NDy [/NDy].
by apply/E_closed=> Ex; apply: DEx; apply: filterS Ex=> y NEy [_ /NEy].
Qed.

(* Lemma closedU (D E : set T) : closed D -> closed E -> closed (D `|` E). *)
(* Proof. *)
(* move=> /openN ND_open /openN NE_open x DEx. *)
(* have := openI ND_open NE_open. *)
(* Qed. *)

Lemma closedT : closed setT. Proof. by []. Qed.

Lemma closed0 : closed set0.
Proof. by move=> x x0; apply: x0; exists [posreal of 1] => ???. Qed.

End Closed.

Lemma closed_comp {T U : uniformType} (f : T -> U) (D : set U) :
  {in ~` f @^-1` D, continuous f} -> closed D -> closed (f @^-1` D).
Proof.
move=> f_cont D_closed x /= xDf; apply: D_closed; apply: contrap xDf => fxD.
have NDfx: ~ D (f x) by move: fxD => [e]; apply.
by apply: f_cont fxD; rewrite in_setE.
Qed.

Lemma closed_filterlim_loc {T} {U : uniformType} {F} {FF : ProperFilter F}
  (f : T -> U) (D : U -> Prop) :
  forall y, f @ F --> y -> F (f @^-1` D) -> closed D -> D y.
Proof.
move=> y Ffy Df CD; apply: CD => yND; apply: filter_not_empty; near x.
  suff [//] : D (f x) /\ ~ D (f x); split; assume_near x.
by end_near; exact: (Ffy _ yND).
Qed.

Lemma closed_filterlim {T} {U : uniformType} {F} {FF : ProperFilter F}
  (f : T -> U) (D : U -> Prop) :
  forall y, f @ F --> y -> (forall x, D (f x)) -> closed D -> D y.
Proof.
by move=> y fy FDf; apply: (closed_filterlim_loc fy); apply: filter_forall.
Qed.

(** ** Complete uniform spaces *)

Definition cauchy {T : uniformType} (F : set (set T)) :=
  forall eps : posreal, exists x, F (ball x eps).

Lemma cvg_cauchy {T : uniformType} (F : set (set T)) :
  [cvg F in T] -> cauchy F.
Proof. by move=> [l /= Fl] eps; exists l; apply/Fl/locally_ball. Qed.

Module Complete.

Definition axiom (T : uniformType) :=
  forall (F : set (set T)), ProperFilter F -> cauchy F -> F --> lim F.

Section ClassDef.

Record class_of (T : Type) := Class {
  base : Uniform.class_of T ;
  mixin : axiom (Uniform.Pack base T)
}.
Local Coercion base : class_of >-> Uniform.class_of.
Local Coercion mixin : class_of >-> Complete.axiom.

Structure type := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).

Definition class := let: Pack _ c _ := cT return class_of cT in c.

Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 (m0 : axiom (@Uniform.Pack T b0 T)) :=
  fun bT b of phant_id (Uniform.class bT) b =>
  fun m of phant_id m m0 => @Pack T (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition uniformType := @Uniform.Pack cT xclass xT.

End ClassDef.

Module Exports.

Coercion base : class_of >-> Uniform.class_of.
Coercion mixin : class_of >-> axiom.
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
Proof. by case: T F FF => [? [?]]. Qed.

Lemma iota_correct_weak (P : T -> Prop) :
  (forall x y, P x -> P y -> close x y) ->
  forall x, P x -> close (iota P) x.
Proof. by move=> HP x Hx eps; apply: HP=> //; apply: getP Hx. Qed.

Lemma close_iota (P Q : T -> Prop) : (forall x, P x <-> Q x) ->
  close (iota P) (iota Q).
Proof. by move=> ?; rewrite (_ : P = Q) // funeqE => x; rewrite propeqE. Qed.

End completeType1.
Arguments complete_cauchy {T} F {FF} _.

Section fct_Complete.

Context {T : choiceType} {U : completeType}.

Lemma complete_cauchy_fct (F : set (set (T -> U))) :
  ProperFilter F -> cauchy F -> F --> lim F.
Proof.
move=> FF Fcauchy; pose G t P := F [set g | P (g t)].
have FG t : ProperFilter (G t).
   by apply: Build_ProperFilter'; apply: filter_not_empty.
have /(_ _) /complete_cauchy Gl : forall t, cauchy (G t).
  by move=> t e; have [f /filterS Ff] := Fcauchy e; exists (f t); apply: Ff.
apply/limP; exists (fun t => lim (G t)); apply/flim_ballP => e /=.
(* TODO: find a way not to pose e / 2 / 2 explicitly *)
have [/= f Ff] := Fcauchy [posreal of e / 2 / 2]; near g.
  apply: (@ball_split _ f); last exact: ball_split (near Ff g _).
  move=> t; have_near (G t) x.
    by apply: (ball_splitl (near (flim_ball (Gl t) _) x _)); assume_near x.
  by end_near; rewrite /G /=; apply: filterS (Ff).
by end_near.
Qed.

Canonical fct_completeType := CompleteType (T -> U) complete_cauchy_fct.

End fct_Complete.

(** ** Limit switching *)

Section Filterlim_switch.

Context {T1 T2 : choiceType}.

Lemma near2P {T U} {F : set (set T)} {G : set (set U)}
   {FF : Filter F} {FG : Filter G} (P : T -> U -> Prop) :
  {near (F, G), forall x, P x.1 x.2} -> {near F & G, forall x y, P x y}.
Proof.
move=> [_ /= [Q1 FQ1 [Q2 GQ2 <-]] Qsub].
apply: filterS FQ1 => x Q1x; apply: filterS GQ2 => y Q2y.
by rewrite -[P _ _]/(P (x, y).1 (x, y).2); apply: Qsub.
Qed.

(* :TODO: Use bigenough reasonning here *)
Lemma filterlim_switch_1 {U : uniformType}
  F1 {FF1 : ProperFilter F1} F2 {FF2 : Filter F2}
  (f : T1 -> T2 -> U) (g : T2 -> U) (h : T1 -> U) (l : U) :
  f @ F1 --> g -> (forall x, f x @ F2 --> h x) -> h @ F1 --> l ->
  g @ F2 --> l.
Proof.
move=> fg fh hl; apply/filterlim_locally => eps /=.
have_near F1 x; first near y.
+ apply: (@ball_split _ (h x)); first by assume_near x.
  apply: (@ball_split _ (f x y)); first by assume_near y.
  by apply/ball_sym; move: (y); assume_near x.
+ by end_near; apply/fh/locally_ball.
end_near; first by apply/hl/locally_ball.
by have /filterlim_locally /= := fg; apply.
Qed.

(* :TODO: Use bigenough reasonning here *)
Lemma filterlim_switch_2 {U : completeType}
  F1 {FF1 : ProperFilter F1} F2 {FF2 : ProperFilter F2}
  (f : T1 -> T2 -> U) (g : T2 -> U) (h : T1 -> U) :
  f @ F1 --> g -> (forall x, f x @ F2 --> h x) ->
  [cvg h @ F1 in U].
Proof.
move=> fg fh; rewrite cvgE; apply: complete_cauchy => e /=.
have_near F1 x; [exists (h x); near x'; [have_near F2 y| ] |].
+ apply: (@ball_splitl _ (f x y)); first by assume_near y.
  apply: (@ball_split _ (f x' y)); first by assume_near y.
  by apply: (@ball_splitr _ (g y)); move: (y); [assume_near x'|assume_near x].
+ by end_near; apply/fh/locally_ball.
+ by end_near; have /filterlim_locally /= := fg; apply.
+ by end_near; have /filterlim_locally /= := fg; apply.
Qed.

(* Alternative version *)
(* Lemma filterlim_switch {U : completeType} *)
(*   F1 (FF1 : ProperFilter F1) F2 (FF2 : ProperFilter F2) (f : T1 -> T2 -> U) (g : T2 -> U) (h : T1 -> U) : *)
(*   [cvg f @ F1 in T2 -> U] -> (forall x, [cvg f x @ F2 in U]) -> *)
(*   [/\ [cvg [lim f @ F1] @ F2 in U], [cvg (fun x => [lim f x @ F2]) @ F1 in U] *)
(*   & [lim [lim f @ F1] @ F2] = [lim (fun x => [lim f x @ F2]) @ F1]]. *)
Lemma filterlim_switch {U : completeType}
  F1 (FF1 : ProperFilter F1) F2 (FF2 : ProperFilter F2)
  (f : T1 -> T2 -> U) (g : T2 -> U) (h : T1 -> U) :
  f @ F1 --> g -> (forall x, f x @ F2 --> h x) ->
  exists l : U, h @ F1 --> l /\ g @ F2 --> l.
Proof.
move=> Hfg Hfh; have [l hl] := filterlim_switch_2 Hfg Hfh.
by exists l; split=> //; apply: filterlim_switch_1 Hfg Hfh hl.
Qed.

End Filterlim_switch.

(** ** Modules with a norm *)

Module NormedModule.

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
  fun bT b & phant_id (@GRing.Lmodule.class K phK bT) b =>
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

Definition norm {K : absRingType} {V : normedModType K} : V -> R :=
  NormedModule.norm (NormedModule.class _).
Definition norm_factor {K : absRingType} (V : normedModType K) : R :=
 @NormedModule.norm_factor _ _ _ (@NormedModule.class _ _ V).
Notation "`|[ x ]|" := (norm x) : ring_scope.

Section NormedModule1.
Context {K : absRingType} {V : normedModType K}.
Implicit Types (l : K) (x y : V) (eps : posreal).

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
Lemma eq_close x y : close x y -> x = y. by rewrite closeE. Qed.

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
Proof. apply/RltP; rewrite subrr normm0; exact: cond_pos. Qed.

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

Lemma flim_unique {F} {FF : ProperFilter F} :
  is_prop [set x : V | F --> x].
Proof. by move=> Fx Fy; rewrite -closeE; apply: is_filter_lim_close. Qed.

Lemma is_filter_lim_locally_unique (x y : V) : x --> y -> x = y.
Proof. move=> H; rewrite -closeE; by apply/is_filter_lim_locally_close. Qed.

End NormedModule1.

Section NormedModule2.

Context {T : Type} {K : absRingType} {V : normedModType K}.

Lemma filterlim_locally_unique {F} {FF : ProperFilter F} (f : T -> V) :
  is_prop [set x : V | f @ F --> x]. (* compat *)
Proof. exact: flim_unique. Qed.

Lemma flimi_unique {F} {FF : ProperFilter F} (f : T -> set V) :
  {near F, is_fun f} -> is_prop [set x : V | f `@ F --> x].
Proof. by move=> ffun fx fy; rewrite -closeE; apply: flimi_close. Qed.
Definition filterlimi_locally_unique := @flimi_unique.

Lemma flim_normP {F : set (set V)} {FF : Filter F} (y : V) :
  F --> y <-> forall eps : posreal, {near F, forall y', `|[y - y']| < eps}.
Proof.
by rewrite !filter_ofE /= -locally_locally_norm; apply: filter_fromP.
Qed.

Lemma flim_norm {F : set (set V)} {FF : Filter F} (y : V) :
  F --> y -> forall eps, eps > 0 -> {near F, forall y', `|[y - y']| < eps}.
Proof. by move=> /flim_normP /(_ (PosReal _)). Qed.

Lemma flim_bounded {F : set (set V)} {FF : Filter F} (y : V) :
  F --> y -> forall M, M > `|[y]| -> {near F, forall y', `|[y']|%real < M}.
Proof.
move=> /flim_norm Fy M; rewrite -subr_gt0 => subM_gt0; have := Fy _ subM_gt0.
apply: filterS => y' yy'; rewrite -(@ltr_add2r _ (- `|[y]|)).
rewrite (ler_lt_trans _ yy') //.
by rewrite (ler_trans _ (ler_distm_dist _ _)) // absRE distrC ler_norm.
Qed.

End NormedModule2.
Hint Resolve normm_ge0.
Arguments flim_norm {_ _ F FF}.
Arguments flim_bounded {_ _ F FF}.
(** Rings with absolute values are normed modules *)

Section AbsRing_NormedModule.

Variable (K : absRingType).
Implicit Types (x y : K) (eps : posreal).

Lemma sub_abs_ball x y eps : `|x - y| < eps -> ball x eps y.
Proof. by []. Qed.

Lemma sub_ball_abs x y eps : ball x eps y -> `|x - y| < 1 * pos eps.
Proof. by rewrite mul1r. Qed.

Definition AbsRing_NormedModMixin := @NormedModule.Mixin K _ _
  (abs : K^o -> R) 1 ler_abs_add absrM sub_abs_ball sub_ball_abs absr0_eq0.

Canonical AbsRing_NormedModType := NormedModType K K^o AbsRing_NormedModMixin.

End AbsRing_NormedModule.

(* Quick fix for non inferred instances *)
(* This does not fix everything, see below *)
Instance NormedModule_locally_filter (K : absRingType) (V : normedModType K)
  (p : V) :
  @ProperFilter (@NormedModule.sort K (Phant K) V)
  (@locally (@NormedModule.uniformType K (Phant K) V) p).
Proof. exact: locally_filter. Qed.

(** Normed vector spaces have some continuous functions *)

Section NVS_continuity.

Context {K : absRingType} {V : normedModType K}.

Lemma locally_pair {U1 U2 : uniformType} (x : U1) (y : U2) :
  locally (x, y) = filter_prod (locally x) (locally y).
Proof.
rewrite funeqE => /= P; rewrite propeqE; split=> /=.
  move=> [e bP]; exists (ball x e `*` ball y e)=> //; last first.
  by exists (ball x e) => //; exists (ball y e) => //.
move=> [? [A [e subA [B [e' subB] <-]]] subP].
exists [posreal of minr (e : R) (e' : R)]%R.
move=> [a b] [/= xa yb]; apply: subP; split => /=.
  by apply: subA; apply: ball_ler xa; rewrite ler_minl lerr.
by apply: subB; apply: ball_ler yb; rewrite ler_minl lerr orbT.
Qed.

(* :TODO: put again filter inside uniform type and prove this instead: *)
(* Lemma filterlim_plus : continuous (fun z : V * V => z.1 + z.2). *)
Lemma flim_add (x y : V) : z.1 + z.2 @[z --> (x, y)] --> x + y.
Proof.
apply/flim_normP=> e; rewrite /=; near z.
  rewrite opprD addrACA (double_var e) (ler_lt_trans (ler_normm_add _ _)) //.
  by rewrite ltr_add //; assume_near z.
by end_near; [apply (flim_norm _ flim_fst)|apply (flim_norm _ flim_snd)].
Qed.

(* Lemma filterlim_scal : continuous (fun z : K * V => z.1 *: z.2). *)
Lemma flim_scal (k : K) (x : V) : z.1 *: z.2 @[z --> (k, x)] --> k *: x.
Proof.
apply/flim_normP=> /= e; rewrite /ball_norm /=; near z.
  rewrite (@subr_trans _ (k *: z.2)).
  rewrite (double_var e) (ler_lt_trans (ler_normm_add _ _)) //.
  rewrite ltr_add // -?(scalerBr, scalerBl).
    rewrite (ler_lt_trans (ler_normmZ _ _)) //.
    rewrite (ler_lt_trans (ler_pmul _ _ (_ : _ <= `|k|%real + 1) (lerr _)))
            ?ler_addl//.
    rewrite -ltr_pdivl_mull // ?(ltr_le_trans ltr01) ?ler_addr //.
    by assume_near z.
  rewrite (ler_lt_trans (ler_normmZ _ _)) //.
  rewrite (ler_lt_trans (ler_pmul _ _ (lerr _) (_ : _ <= `|[x]| + 1))) //.
    by rewrite ltrW //; assume_near z.
  rewrite -ltr_pdivl_mulr // ?(ltr_le_trans ltr01) ?ler_addr //.
  by assume_near z.
end_near.
- by apply (flim_norm _ flim_snd); rewrite mulr_gt0 // ?invr_gt0 ltr_paddl.
- by apply (flim_bounded _ flim_snd); rewrite ltr_addl.
- apply (flim_norm (_ : K^o) flim_fst).
  by rewrite mulr_gt0// ?invr_gt0 ltr_paddl.
Qed.
Arguments flim_scal k x : clear implicits.

Lemma flim_scalr (k : K) (x : V) : k *: z @[z --> x] --> k *: x.
Proof. exact: (flim_comp2 (flim_const _) flim_id (flim_scal _ _)). Qed.

Lemma flim_scall (l : K) (x : V) : k *: x @[k --> l] --> l *: x.
Proof. exact: (flim_comp2 flim_id (flim_const _) (flim_scal _ _)). Qed.

Lemma flim_opp (x : V) : (@GRing.opp V) @ x --> - x.
Proof.
rewrite -scaleN1r => P /flim_scalr /=.
by apply: filterS => x'; rewrite scaleN1r.
Qed.

Definition filterlim_plus := @flim_add. (*compat*)
Definition filterlim_scal := @flim_scal. (*compat*)
Definition filterlim_scal_l := @flim_scall. (*compat*)
Definition filterlim_scal_r := @flim_scalr. (*compat*)
Definition filterlim_opp := @flim_opp. (*compat*)

End NVS_continuity.

Lemma filterlim_mult {K : absRingType} (x y : K) :
   z.1 * z.2 @[z --> (x, y)] --> x * y.
Proof. exact: (@flim_scal _ (AbsRing_NormedModType K)). Qed.


(** ** Complete Normed Modules *)

Module CompleteNormedModule.

Section ClassDef.

Variable K : absRingType.

Record class_of (T : Type) := Class {
  base : NormedModule.class_of K T ;
  mixin : Complete.axiom (Uniform.Pack base T)
}.
Local Coercion base : class_of >-> NormedModule.class_of.
Definition base2 T (cT : class_of T) : Complete.class_of T :=
  @Complete.Class _ (@base T cT) (@mixin T cT).
Local Coercion base2 : class_of >-> Complete.class_of.

Structure type (phK : phant K) := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.

Variables (phK : phant K) (cT : type phK) (T : Type).

Definition class := let: Pack _ c _ := cT return class_of cT in c.

Definition pack :=
  fun bT b & phant_id (@NormedModule.class K phK bT) (b : NormedModule.class_of K T) =>
  fun mT m & phant_id (@Complete.class mT) (@Complete.Class T b m) =>
    Pack phK (@Class T b m) T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @GRing.Zmodule.Pack cT xclass xT.
Definition lmodType := @GRing.Lmodule.Pack K phK cT xclass xT.
Definition uniformType := @Uniform.Pack cT xclass xT.
Definition join_zmodType := @GRing.Zmodule.Pack uniformType xclass xT.
Definition join_lmodType := @GRing.Lmodule.Pack K phK uniformType xclass xT.
Definition normedModType := @NormedModule.Pack K phK cT xclass xT.
Definition join_uniformType := @Uniform.Pack normedModType xclass xT.
End ClassDef.

Module Exports.

Coercion base : class_of >-> NormedModule.class_of.
Coercion base2 : class_of >-> Complete.class_of.
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
Coercion normedModType : type >-> NormedModule.type.
Canonical normedModType.
Canonical join_uniformType.
Definition type_canonical_filter
   (K : absRingType) (phK : phant K) (T : type phK) :=
  @CanonicalFilter T T locally.
Coercion type_canonical_filter : type >-> canonical_filter.
Canonical type_canonical_filter.
Notation completeNormedModType K := (type (Phant K)).
Notation "[ 'completeNormedModType' K 'of' T ]" := (@pack _ (Phant K) T _ _ id _ _ id)
  (at level 0, format "[ 'completeNormedModType'  K  'of'  T ]") : form_scope.

End Exports.

End CompleteNormedModule.

Export CompleteNormedModule.Exports.

Section CompleteNormedModule1.

Context {K : absRingType} {V : completeNormedModType K}.

Lemma get_correct (P : V -> Prop) :
  (exists! x : V, P x) -> P (get P).
Proof. by move=> [x [Px _]]; exact: getP Px. Qed.
Definition iota_correct := get_correct.

Lemma get_is_filter_lim {F} {FF : ProperFilter F} (l : V) :
  F --> l -> lim F = l.
Proof.
move=> Fl; have FlF : F --> lim F by rewrite -cvgE; exists l.
by apply: flim_unique.
Qed.

Context {T : Type}.

Lemma get_filterlim_locally {F} {FF : ProperFilter F} (f : T -> V) l :
  f @ F --> l -> lim (f @ F) = l.
Proof. exact: get_is_filter_lim. Qed.

Lemma get_filterlimi_locally {F} {FF : ProperFilter F} (f : T -> V -> Prop) l :
  F (fun x => is_prop (f x)) ->
  f `@ F --> l -> lim (f `@ F) = l.
Proof.
move=> f_prop f_l; apply: get_unique => // l' f_l'.
exact: filterlimi_locally_unique _ f_l' f_l.
Qed.

End CompleteNormedModule1.

(** * Extended Types *)

(** ** Pairs *)

(* TODO a prouver dans Rstruct pour prouver norm_compat1 and norm_compat2 *)
Lemma sqrt_plus_sqr (x y : R) :
  maxr `|x| `|y| <= Num.sqrt (x^+2 + y^+2) <= Num.sqrt 2%:R * maxr `|x| `|y|.
Proof.
rewrite -(@ler_pexpn2r _ 2) ?nnegrE ?sqrtr_ge0 ?ler_maxr ?normr_ge0 // andbC.
rewrite -(@ler_pexpn2r _ 2) ?nnegrE ?mulr_ge0 ?sqrtr_ge0 ?ler_maxr ?normr_ge0 //.
rewrite sqr_sqrtr ?addr_ge0 // ?sqr_ge0 //.
wlog : x y / `|x| <= `|y| => H.
  case: (lerP `|x| `|y|) => yx; first by rewrite H.
  by rewrite maxrC addrC H // ltrW.
rewrite maxr_r ?real_normK ?num_real ?ler_addr ?sqr_ge0 // andbT.
rewrite exprMn_comm ?sqr_sqrtr //; last by rewrite /GRing.comm mulrC.
rewrite -(@real_normK _ x) ?num_real // -{1}(@real_normK _ y) ?num_real //.
by rewrite mulr_natl mulr2n ler_add // ler_pexpn2r // ?num_real ?nnegrE.
Qed.

Section prod_NormedModule.

Context {K : absRingType} {U V : normedModType K}.

Definition prod_norm (x : U * V) := Num.sqrt (`|[x.1]| ^+ 2 + `|[x.2]| ^+ 2).

Lemma prod_norm_triangle : forall x y : U * V, prod_norm (x + y) <= prod_norm x + prod_norm y.
Proof.
intros [xu xv] [yu yv].
rewrite /prod_norm /=.
apply (@ler_trans _ (Num.sqrt ((`|[xu]| + `|[yu]|)^+2 + (`|[xv]| + `|[yv]|)^+2))).
  by rewrite ler_wsqrtr // ler_add // ler_pexpn2r //
     ?nnegrE ?addr_ge0 // ?normm_ge0 // ?norm_triangle.
set a := `|[xu]|. set b := `|[yu]|. set c := `|[xv]|. set d := `|[yv]|.
rewrite -(@ler_pexpn2r _ 2) // ?nnegrE ?ler_add ?addr_ge0 // ?sqrtr_ge0 //.
rewrite sqr_sqrtr ?addr_ge0 // ?sqr_ge0 // [in X in _ <= X]sqrrD.
rewrite !sqr_sqrtr // ?addr_ge0 // ?sqr_ge0 //.
rewrite 2!sqrrD -!addrA ler_add //.
rewrite (addrCA _ (c^+2)) 2!addrCA ler_add //.
rewrite 2!addrCA 2!(addrCA _ (b^+2)) ler_add //.
rewrite !addrA ler_add //.
rewrite -mulr2n -addrA -mulr2n -mulr2n -mulrnDl ler_muln2r /=.
rewrite -sqrtrM ?addr_ge0 // ?sqr_ge0 //.
rewrite -(@ler_pexpn2r _ 2) // ?nnegrE ?sqrtr_ge0 ?addr_ge0 ?mulr_ge0 ?normm_ge0 //.
rewrite sqr_sqrtr ?mulr_ge0 ?addr_ge0 ?sqr_ge0 //.
rewrite sqrrD [in X in _ <= X]mulrDr 2![in X in _ <= X]mulrDl.
rewrite -exprMn_comm ?/GRing.comm; last by rewrite mulrC.
rewrite -!addrA ler_add //.
rewrite -(@exprMn_comm _ c d) ?/GRing.comm; last by rewrite mulrC.
rewrite !addrA ler_add // -mulr2n.
rewrite -(@exprMn_comm _ c b) ?/GRing.comm; last by rewrite mulrC.
rewrite -(@exprMn_comm _ a d) ?/GRing.comm; last by rewrite mulrC.
rewrite -subr_ge0 addrAC.
by rewrite mulrCA (mulrC a b) -mulrA mulrA -sqrrB ?sqr_ge0.
Qed.

Lemma prod_norm_scal (l : K) : forall (x : U * V), prod_norm (l *: x) <= abs l * prod_norm x.
Proof.
case=> xu xv; rewrite /prod_norm /=.
rewrite -(@ler_pexpn2r _ 2) // ?nnegrE ?mulr_ge0 ?sqrtr_ge0 ?absr_ge0 //.
rewrite sqr_sqrtr ?addr_ge0 ?sqr_ge0 //.
rewrite exprMn_comm ?/GRing.comm; last by rewrite mulrC.
rewrite sqr_sqrtr ?addr_ge0 // ?sqr_ge0 // mulrDr.
rewrite -exprMn_comm ?/GRing.comm; last by rewrite mulrC.
rewrite -exprMn_comm ?/GRing.comm; last by rewrite mulrC.
by rewrite ler_add // ler_pexpn2r // ?nnegrE ?mulr_ge0 ?absr_ge0 ?normm_ge0 // ?ler_normmZ.
Qed.

Lemma prod_norm_compat1 : forall (x y : U * V) (eps : R),
  prod_norm (x - y) < eps -> ball x eps y.
Proof.
move=> [xu xv] [yu yv] eps H.
set x := `|[yu - xu]|. set y := `|[yv - xv]|.
rewrite /prod_norm normmB (normmB xv) in H.
case/andP: (sqrt_plus_sqr x y) => /ler_lt_trans/(_ H) => H1.
have /RltP He : 0 < eps by apply: (ler_lt_trans _ H); rewrite sqrtr_ge0.
rewrite (_ : eps = mkposreal _ He) // => H2.
split; apply: norm_compat1; apply: (ler_lt_trans _ H1).
by rewrite ler_maxr /x normmB real_ler_norm // ger0_real // normm_ge0.
by rewrite ler_maxr orbC /y normmB real_ler_norm // ger0_real // normm_ge0.
Qed.

Definition prod_norm_factor :=
  Num.sqrt 2%:R * maxr (@norm_factor K U) (@norm_factor K V).

Lemma prod_norm_compat2 : forall (x y : U * V) (eps : posreal),
  ball x eps y -> (prod_norm (x - y) < prod_norm_factor * eps).
Proof.
move=> [xu xv] [yu yv] eps [Bu Bv].
set x := `|[xu - yu]|. set y := `|[xv - yv]|.
case/andP: (sqrt_plus_sqr x y) => H1 H2; apply: (ler_lt_trans H2).
rewrite /prod_norm_factor -mulrA.
rewrite -subr_gt0 -mulrBr pmulr_rgt0 // ?sqrtr_gt0 // subr_gt0 maxr_pmull //.
case: (lerP `|y| `|x|) => yx.
  rewrite [in X in X < _]maxr_l //.
  rewrite (@ltr_le_trans _ (norm_factor U * eps)) ?ler_maxr ?lerr //.
  rewrite ger0_norm ?normm_ge0 //; exact: norm_compat2.
rewrite (@maxr_r _ _ `|y|%R); last by rewrite ltrW.
rewrite (@ltr_le_trans _ (norm_factor V * eps)) // ?ler_maxr ?lerr ?orbT //.
rewrite ger0_norm ?normm_ge0 //; exact: norm_compat2.
Qed.

Lemma prod_norm_eq_zero : forall x : U * V, prod_norm x = 0 -> x = 0.
Proof.
move=> [xu xv] /eqP H.
rewrite sqrtr_eq0 ler_eqVlt ltrNge addr_ge0  ?sqr_ge0 // orbF in H.
rewrite paddr_eq0 ?sqr_ge0 // 2!sqrf_eq0 /= 2!normm_eq0 in H.
by case/andP : H => /eqP -> /eqP ->.
Qed.

End prod_NormedModule.

Definition prod_NormedModule_mixin (K : absRingType) (U V : normedModType K) :=
  @NormedModMixin K _ _ (@prod_norm K U V) prod_norm_factor prod_norm_triangle
  prod_norm_scal prod_norm_compat1 prod_norm_compat2 prod_norm_eq_zero.

Canonical prod_NormedModule (K : absRingType) (U V : normedModType K) :=
  NormedModType K (U * V) (@prod_NormedModule_mixin K U V).

Lemma norm_prod {K : absRingType} {U : normedModType K} {V : normedModType K}
  (x : U) (y : V) :
  maxr `|[ x ]| `|[ y ]| <= `|[(x, y)]| <= Num.sqrt 2%:R * maxr `|[x]| `|[y]|.
Proof.
by rewrite -(ger0_norm (normm_ge0 _)) -(ger0_norm (normm_ge0 y)) sqrt_plus_sqr.
Qed.

(** *)

(** * The topology on natural numbers *)

(* :TODO: FIXME *)
Definition eventually (P : nat -> Prop) :=
  exists N : nat, forall n, (N <= n)%N -> P n.

Notation "'\oo'" := eventually : classical_set_scope.

Global Instance eventually_filter : ProperFilter eventually.
Proof.
constructor; first by case=> n; apply; apply leqnn.
constructor.
- by exists O.
- move=> P Q [NP HP] [NQ HQ].
  exists (maxn NP NQ) => n Hn; split.
  by apply/HP/(leq_trans _ Hn)/leq_maxl.
  by apply/HQ/(leq_trans _ Hn)/leq_maxr.
- by move=> P Q H [NP HP]; exists NP => n Hn; apply/H/HP.
Qed.

(** * The topology on real numbers *)

Definition R_AbsRing_mixin :=
  @AbsRingMixin [ringType of R] _ absr0 absrN1 ler_abs_add absrM absr0_eq0.
Canonical R_AbsRing := @AbsRingType R R_AbsRing_mixin.
Definition R_uniformType_mixin := AbsRingUniformMixin R_AbsRing.

Canonical R_uniformType := UniformType R R_uniformType_mixin.
(*NB: already exists Canonical R_canonical_filter := @CanonicalFilter R R locally.*)

(* TODO: Remove R_complete_lim and use lim instead *)
Definition R_complete_lim (F : (R -> Prop) -> Prop) : R :=
  real (Lub_Rbar (fun x : R => F (ball (x + 1) [posreal of 1]))).

Lemma R_complete_ax1 (F : set (set R)) : ProperFilter F ->
  (forall eps : posreal, exists x : R, F (ball x eps)) ->
  forall eps : posreal, F (ball (R_complete_lim F) eps).
Proof.
move=> FF HF eps.
rewrite /R_complete_lim.
move: (Lub_Rbar_correct (fun x : R => F (ball (x + 1) [posreal of 1]))).
move Hl : (Lub_Rbar _) => l{Hl}; move: l => [x| |] [Hx1 Hx2].
- case: (HF [posreal of Num.min 2%:R (pos eps) / 2]) => z Hz.
  have H1 : z - Num.min 2%:R (pos eps) / 2%:R + 1 <= x + 1.
    rewrite ler_add //; apply/RleP/Hx1.
    apply: filterS Hz.
    rewrite /ball /= => u; rewrite /AbsRing_ball absrB ltr_distl.
    rewrite absrB ltr_distl RdivE //.
    case/andP => {Hx1 Hx2 FF HF x F} Bu1 Bu2.
    have H : Num.min 2%:R (pos eps) <= 2%:R by rewrite ler_minl lerr.
    rewrite addrK -addrA Bu1 /= (ltr_le_trans Bu2) //.
    rewrite -addrA ler_add // -addrA addrC ler_subr_addl.
    by rewrite ler_add // ler_pdivr_mulr // ?mul1r.
  have H2 : x + 1 <= z + Num.min 2%:R (pos eps) / 2%:R + 1.
    rewrite ler_add //; apply/RleP/(Hx2 (Finite _)) => v Hv.
    apply Rbar_not_lt_le => /RltP Hlt.
    apply: filter_not_empty.
    apply: filterS (filterI Hz Hv).
    rewrite /ball /= => w []; rewrite /AbsRing_ball.
    rewrite RdivE // absrB ltr_distl => /andP[_ Hw1].
    rewrite absrB ltr_distl addrK => /andP[Hw2 _].
    move: (ltr_trans (ltr_trans Hw1 Hlt) Hw2); by rewrite ltrr.
  apply: filterS Hz.
  rewrite /ball /= => u; rewrite /AbsRing_ball absrB absRE 2!ltr_distl.
  case/andP => {Hx1 Hx2 F FF HF} H H0.
  have H3 : Num.min 2%:R (pos eps) <= eps by rewrite ler_minl lerr orbT.
  apply/andP; split.
  - move: H1; rewrite -ler_subr_addr addrK ler_subl_addr => H1.
    rewrite ltr_subl_addr // (ltr_le_trans H0) //.
    rewrite !RdivE // -ler_subr_addr (ler_trans H1) //.
    rewrite -ler_subr_addl -!addrA (addrC x) !addrA subrK.
    rewrite ler_subr_addr -mulrDl ler_pdivr_mulr //.
    by rewrite -mulr2n -mulr_natl mulrC ler_pmul.
  - move: H2; rewrite -ler_subr_addr addrK.
    move/ler_lt_trans; apply.
    move: H; rewrite !RdivE // ltr_subl_addr => H.
    rewrite -ltr_subr_addr (ltr_le_trans H) //.
    rewrite addrC -ler_subr_addr -!addrA (addrC u) !addrA subrK.
    rewrite -ler_subl_addr opprK -mulrDl ler_pdivr_mulr // -mulr2n -mulr_natl.
    by rewrite mulrC ler_pmul.
- case (HF [posreal of 1]) => y Fy.
  case: (Hx2 (y + 1)) => x Fx.
  apply Rbar_not_lt_le => Hlt.
  apply: filter_not_empty.
  apply: filterS (filterI Fy Fx) => z [Hz1 Hz2].
  apply: Rbar_le_not_lt Hlt;  apply/RleP.
  rewrite -(ler_add2r (-(y - 1))) opprB !addrA -![in X in _ <= X]addrA.
  rewrite (addrC y) ![in X in _ <= X]addrA subrK.
  suff : `|x + 1 - y|%R <= 1 + 1 by rewrite ler_norml => /andP[].
  rewrite ltrW // (@subr_trans _ z).
  by rewrite (ler_lt_trans (ler_norm_add _ _)) // ltr_add // distrC.
- case: (HF [posreal of 1]) => y Fy.
  case: (Hx1 (y - 1)); by rewrite addrAC addrK.
Qed.

Lemma R_complete (F : (R -> Prop) -> Prop) :
  ProperFilter F -> cauchy F -> F --> lim F.
Proof.
move=> FF F_cauchy; rewrite -cvgE.
exists (R_complete_lim F).
apply/filterlim_locally => /=.
exact: R_complete_ax1.
Qed.

Canonical R_completeType := CompleteType R R_complete.

Canonical R_NormedModule := [normedModType R of R^o].
Canonical R_CompleteNormedModule := [completeNormedModType R of R^o].

Definition at_left x := within (fun u : R => u < x) (locally x).
Definition at_right x := within (fun u : R => x < u) (locally x).
(* :TODO: We should have filter notation ^- and ^+ for these *)

Global Instance at_right_proper_filter : forall (x : R),
  ProperFilter (at_right x).
Proof.
move=> x.
constructor; last by apply within_filter, locally_filter.
case=> d /(_ (x + pos d / 2%:R)).
apply; last by rewrite ltr_addl.
apply sub_abs_ball.
rewrite opprD !addrA subrr add0r absrN absRE normf_div !ger0_norm //.
by rewrite ltr_pdivr_mulr // ltr_pmulr // (_ : 1 = 1%:R) // ltr_nat.
Qed.

Global Instance at_left_proper_filter : forall (x : R),
  ProperFilter (at_left x).
move=> x.
constructor; last by apply within_filter, locally_filter.
case=> d /(_ (x - pos d / 2%:R)).
apply; last by rewrite ltr_subl_addl ltr_addr.
apply sub_abs_ball.
rewrite opprD !addrA subrr add0r opprK absRE normf_div !ger0_norm //.
by rewrite ltr_pdivr_mulr // ltr_pmulr // (_ : 1 = 1%:R) // ltr_nat.
Qed.

(** Continuity of norm *)

Lemma filterlim_norm {K : absRingType} {V : normedModType K} :
  forall (x : V), norm @ x --> (norm x).
Proof.
intros x.
apply (@filterlim_filter_le_1 _ _ _ _ _ _ (@locally_le_locally_norm _ _ x)).
eapply (proj2 (@filterlim_locally _ _ _ _)) => eps /=.
exists eps => /= y Hy.
by apply/sub_abs_ball/(ler_lt_trans (norm_triangle_inv _ _)).
Qed.

(* :TODO: yet, not used anywhere?! *)
Lemma filterlim_norm_zero {U} {K : absRingType} {V : normedModType K}
  {F : set (set U)} {FF : Filter F} (f : U -> V) :
  (fun x => `|[f x]|) @ F --> (0 : R)
  -> f @ F --> (0 : V).
Proof.
  (* intros Hf. *)
  (* apply filterlim_locally_ball_norm => eps. *)
  (* generalize (proj1 (filterlim_locally_ball_norm _ _) Hf eps) ; *)
  (* unfold ball_norm ; simpl. *)
  (* apply filterS => /= x. *)
  (* rewrite !minus_zero_r {1}/norm /= /abs /= Rabs_pos_eq //. *)
  (* by apply norm_ge_0. *)
(*Qed.*)
Admitted.

Canonical eventually_filter_source X :=
  @CanonicalFilterSource X _ nat (fun f => f @ \oo).

(* :TODO: finish the commented proof to derive the result from
          filterlim_bound and change names *)
Lemma filterlim_bounded {K : absRingType} {V : normedModType K} (a : nat -> V) :
  (exists x : V, a --> x)
 -> {M : R | forall n, norm (a n) <= M}.
Proof.
(* rewrite -/[cvg a in V] cvgE => a_cvg. *)
(* have: exists M, forall n, norm (a n) <= M. *)
(*   have [] := !! flim_bounded _ a_cvg (`|[lim (a @ \oo)]| + 1). *)
(*     by rewrite ltr_addl. *)
(*   move=> N /= ltN. *)
(*   exists (maxn (\bigmax_(i < N) *)
move=> Ha.
have {Ha}H : exists x : R, (fun n => `|[a n]|) --> x.
  case: Ha => [l Hl].
  exists `|[ l ]|; exact: (filterlim_comp Hl (@filterlim_norm _ _ _)).
case: (LPO_ub_dec (fun n => norm (a n))) => [[M HM] | HM].
  exists M => n; by apply/RleP.
exfalso.
case: H => l Hl.
have {Hl} := proj1 (@filterlim_locally _ _ _ l) Hl [posreal of 1].
rewrite /= /ball /= /AbsRing_ball => -[N HN].
move: (HM (seq.foldr Num.max (1 + l) (seq.map (fun n => `|[a n]|) (seq.iota 0 N)))) => {HM}.
case => [n].
move/RltP; apply/negP; rewrite -lerNgt.
elim: N a n HN => /=[ |N IH] a n HN.
  move: (HN n (leq0n _)).
  rewrite ltr_distl => /andP[].
  by rewrite ltr_subl_addl => ? _; apply/ltrW.
case: n => [ | n]; first by rewrite ler_maxr lerr.
rewrite ler_maxr; apply/orP; right.
eapply ler_trans.
  apply (IH (fun n => a n.+1)) => k Hk; by apply/HN.
rewrite {HN n IH}.
rewrite ler_eqVlt; apply/orP; left; apply/eqP.
by elim: N 0%nat => /=[// |N IH] n0; rewrite IH.
Qed.

(** Some open sets of [R] *)

Lemma open_lt (y : R) : open (fun u : R => u < y).
Proof.
move=> x; rewrite -subr_gt0 => /RltP xy.
exists (mkposreal _ xy) => z /sub_ball_abs.
rewrite /= mul1r absrB ltr_distl => /andP[_ Bz].
by rewrite (_ : y = x + (y - x)) // addrCA subrr addr0.
Qed.

Lemma open_gt (y : R) : open (fun u : R => y < u).
Proof.
move=> x; rewrite -subr_gt0 => /RltP xy.
exists (mkposreal _ xy) => z /sub_ball_abs.
rewrite /= mul1r absrB ltr_distl => /andP[Bz _].
by rewrite (_ : y = x - (x - y)) // opprB addrCA subrr addr0.
Qed.

Definition open_or := @openU. (*compat*)
Definition open_and := @openI. (*compat*)
Definition open_not := @openN. (*compat*)
Definition closed_and := @closedI. (*compat*)
Definition closed_not := @closedN. (*compat*)

Lemma open_neq (y : R) : open (fun u : R => u <> y).
Proof.
apply (@open_ext _ (fun u : R => u < y \/ y < u)).
  split => u.
  by move/orP; rewrite -neqr_lt => /eqP.
  by move/eqP; rewrite neqr_lt => /orP.
apply open_or; by [apply open_lt | apply open_gt].
Qed.

(** Some closed sets of [R] *)

Lemma closed_le (y : R) : closed (fun u : R => u <= y).
Proof.
apply (@closed_ext _ (fun u => not (y < u))) => x.
  by rewrite lerNgt; split => /negP.
apply: closed_not; exact: open_gt.
Qed.

Lemma closed_ge (y : R) : closed (fun u : R => y <= u).
Proof.
apply (@closed_ext _ (fun u : R => not (u < y))) => x.
  by rewrite lerNgt; split => /negP.
apply: closed_not; exact: open_lt.
Qed.

Lemma closed_eq (y : R) : closed (fun u : R => u = y).
Proof.
apply (@closed_ext _ (fun u => not (u <> y))) => x.
  destruct (Req_dec x y); by tauto.
apply: closed_not; exact: open_neq.
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
apply Hp ; apply Hd; apply/RltP => //; move/sub_ball_abs : Hy;
  by rewrite mul1r absrB.
Qed.

(** * Topology on [R]² *)

(* ALTERNATIVE: *)
Definition locally_2d (x y : R) (P : R -> R -> Prop) := locally (x, y) (fun z => P z.1 z.2).
(* Should prove equivalence with prod_filter formulation *)
(* and deduce everything from it *)

(*Definition locally_2d (P : R -> R -> Prop) x y :=
  exists delta : posreal, forall u v, Rabs (u - x) < delta -> Rabs (v - y) < delta -> P u v.*)

Lemma locally_2d_locally P x y :
  locally_2d x y P <-> locally (x,y) (fun z => P (fst z) (snd z)).
Proof. split; move=> [d H]; exists d; exact H. Qed.

Lemma locally_2d_impl_strong (P Q : R -> R -> Prop) x y :
  locally_2d x y (fun u v => locally_2d u v P -> Q u v) ->
  locally_2d x y P -> locally_2d x y Q.
Proof.
move=> /locally_2d_locally Li /locally_2d_locally/locally_locally LP.
apply locally_2d_locally.
apply: filterS (filterI Li LP) => uv -[H1 H2].
by apply/H1/locally_2d_locally.
Qed.

Lemma locally_2d_singleton (P : R -> R -> Prop) x y : locally_2d x y P -> P x y.
Proof. by move/locally_2d_locally => /locally_singleton. Qed.

Lemma locally_2d_impl (P Q : R -> R -> Prop) x y :
  locally_2d x y (fun u v => P u v -> Q u v) ->
  locally_2d x y P -> locally_2d x y Q.
Proof.
move=> H.
apply locally_2d_impl_strong.
case : H => d Hd.
exists d => /= z Hz HP.
by apply/(Hd _ Hz); apply locally_2d_singleton.
Qed.

Lemma locally_2d_forall (P : R -> R -> Prop) x y :
  (forall u v, P u v) -> locally_2d x y P.
Proof. move=> Hp; by exists [posreal of 1]. Qed.

Lemma locally_2d_and (P Q : R -> R -> Prop) x y :
  locally_2d x y P -> locally_2d x y Q -> locally_2d x y (fun u v => P u v /\ Q u v).
Proof.
intros H.
apply: locally_2d_impl.
apply: locally_2d_impl H.
apply locally_2d_forall.
now split.
Qed.

Lemma locally_2d_align :
  forall (P Q : R -> R -> Prop) x y,
  ( forall eps : posreal, (forall uv, ball (x, y) eps uv -> P uv.1 uv.2) ->
    forall uv, ball (x, y) eps uv -> Q uv.1 uv.2 ) ->
  locally_2d x y P -> locally_2d x y Q.
Proof.
intros P Q x y K (d,H).
exists d => uv Huv.
by apply (K d) => //.
Qed.

Lemma locally_2d_1d_const_x :
  forall (P : R -> R -> Prop) x y,
  locally_2d x y P ->
  locally y (fun t => P x t).
Proof.
intros P x y (d,Hd).
exists d; intros z Hz.
by apply (Hd (x, z)).
Qed.

Lemma locally_2d_1d_const_y :
  forall (P : R -> R -> Prop) x y,
  locally_2d x y P ->
  locally x (fun t => P t y).
Proof.
intros P x y (d,Hd).
exists d; intros z Hz.
by apply (Hd (z, y)).
Qed.

Lemma locally_2d_1d_strong :
  forall (P : R -> R -> Prop) x y,
  locally_2d x y P ->
  locally_2d x y (fun u v => forall (t : R), 0 <= t <= 1 ->
    locally t (fun z => locally_2d (x + z * (u - x)) (y + z * (v - y)) P)).
Proof.
move=> P x y.
apply locally_2d_align => eps HP uv Huv t Ht.
set u := uv.1. set v := uv.2.
have Zm : 0 <= Num.max `|u - x| `|v - y| by rewrite ler_maxr 2!normr_ge0.
rewrite ler_eqVlt in Zm.
case/orP : Zm => Zm.
- apply filter_forall => z.
  exists eps => pq.
  rewrite !(RminusE,RmultE,RplusE).
  move: (Zm).
  have : Num.max `|u - x| `|v - y| <= 0 by rewrite -(eqP Zm).
  rewrite ler_maxl => /andP[H1 H2] _.
  rewrite (_ : u - x = 0); last by apply/eqP; rewrite -normr_le0.
  rewrite (_ : v - y = 0); last by apply/eqP; rewrite -normr_le0.
  rewrite !(mulr0,addr0); by apply HP.
- have : Num.max (`|u - x|) (`|v - y|) < eps.
    rewrite ltr_maxl; apply/andP; split.
    - case: Huv => /sub_ball_abs /=; by rewrite mul1r absrB.
    - case: Huv => _ /sub_ball_abs /=; by rewrite mul1r absrB.
  rewrite -subr_gt0 => /RltP H1.
  set d1 := mkposreal _ H1.
  have /RltP H2 : 0 < pos d1 / 2%:R / Num.max `|u - x| `|v - y|
    by rewrite mulr_gt0 // invr_gt0.
  set d2 := mkposreal _ H2.
  exists d2 => z Hz.
  exists [posreal of d1 / 2] => /= pq Hpq.
  set p := pq.1. set q := pq.2.
  apply HP; split.
  + apply/sub_abs_ball => /=.
    rewrite absrB.
    rewrite (_ : p - x = p - (x + z * (u - x)) + (z - t + t) * (u - x)); last first.
      by rewrite subrK opprD addrA subrK.
    apply: (ler_lt_trans (ler_abs_add _ _)).
    rewrite (_ : pos eps = pos d1 / 2%:R + (pos eps - pos d1 / 2%:R)); last first.
      by rewrite addrCA subrr addr0.
    rewrite (_ : pos eps - _ = d1) // in Hpq.
    case: Hpq => /sub_ball_abs Hp /sub_ball_abs Hq.
    rewrite mul1r /= (_ : pos eps - _ = d1) // !(RminusE,RplusE,RmultE,RdivE) // in Hp, Hq.
    rewrite absrB in Hp. rewrite absrB in Hq.
    rewrite (ltr_le_add Hp) // (ler_trans (absrM _ _)) //.
    apply (@ler_trans _ ((pos d2 + 1) * Num.max `|u - x| `|v - y|)).
    apply ler_pmul; [by rewrite normr_ge0 | by rewrite normr_ge0 | | ].
    rewrite (ler_trans (ler_abs_add _ _)) // ler_add //.
    move/sub_ball_abs : Hz; rewrite mul1r => tzd2; by rewrite absrB ltrW.
    rewrite absRE ger0_norm //; by case/andP: Ht.
    by rewrite ler_maxr lerr.
    rewrite /d2 /d1 /=.
    set n := Num.max _ _.
    rewrite mulrDl mul1r -mulrA mulVr ?unitfE ?lt0r_neq0 // mulr1.
    rewrite ler_sub_addr addrAC -mulrDl -mulr2n -mulr_natr.
    by rewrite -mulrA mulrV ?mulr1 ?unitfE // subrK.
  + apply/sub_abs_ball => /=.
    rewrite absrB.
    rewrite (_ : (q - y) = (q - (y + z * (v - y)) + (z - t + t) * (v - y))); last first.
      by rewrite subrK opprD addrA subrK.
    apply: (ler_lt_trans (ler_abs_add _ _)).
    rewrite (_ : pos eps = pos d1 / 2%:R + (pos eps - pos d1 / 2%:R)); last first.
      by rewrite addrCA subrr addr0.
    rewrite (_ : pos eps - _ = d1) // in Hpq.
    case: Hpq => /sub_ball_abs Hp /sub_ball_abs Hq.
    rewrite mul1r /= (_ : pos eps - _ = d1) // !(RminusE,RplusE,RmultE,RdivE) // in Hp, Hq.
    rewrite absrB in Hp. rewrite absrB in Hq.
    rewrite (ltr_le_add Hq) // (ler_trans (absrM _ _)) //.
    rewrite (@ler_trans _ ((pos d2 + 1) * Num.max `|u - x| `|v - y|)) //.
    apply ler_pmul; [by rewrite normr_ge0 | by rewrite normr_ge0 | | ].
    rewrite (ler_trans (ler_abs_add _ _)) // ler_add //.
    move/sub_ball_abs : Hz; rewrite mul1r => tzd2; by rewrite absrB ltrW.
    rewrite absRE ger0_norm //; by case/andP: Ht.
    by rewrite ler_maxr lerr orbT.
    rewrite /d2 /d1 /=.
    set n := Num.max _ _.
    rewrite mulrDl mul1r -mulrA mulVr ?unitfE ?lt0r_neq0 // mulr1.
    rewrite ler_sub_addr addrAC -mulrDl -mulr2n -mulr_natr.
    by rewrite -mulrA mulrV ?mulr1 ?unitfE // subrK.
Qed.

Lemma locally_2d_1d (P : R -> R -> Prop) x y :
  locally_2d x y P ->
  locally_2d x y (fun u v => forall t, 0 <= t <= 1 -> locally_2d (x + t * (u - x)) (y + t * (v - y)) P).
Proof.
move/locally_2d_1d_strong.
apply: locally_2d_impl.
apply locally_2d_forall => u v H t Ht.
specialize (H t Ht).
have : locally t (fun z => locally_2d (x + z * (u - x)) (y + z * (v - y)) P) by [].
by apply: locally_singleton.
Qed.

Lemma locally_2d_ex_dec :
  forall P x y,
  (forall x y, P x y \/ ~P x y) ->
  locally_2d x y P ->
  {d : posreal | forall u v, `|u - x| < d -> `|v - y| < d -> P u v}.
Proof.
intros P x y P_dec H.
destruct (@locally_ex _ (x, y) (fun z => P (fst z) (snd z))) as [d Hd].
- destruct H as [e H].
  exists e.
  intros [u v] Huv.
  by apply/H/Huv.
exists d=>  u v Hu Hv.
by apply (Hd (u, v)) => /=; split; apply sub_abs_ball; rewrite absrB.
Qed.

(** * Some Topology on [Rbar] *)

(* NB: already defined in R_scope in Rbar.v *)
Notation "'+oo'" := p_infty : real_scope.
Notation "'-oo'" := m_infty : real_scope.

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

Canonical Rbar_canonical_filter := @CanonicalFilter R Rbar (Rbar_locally).

Global Instance Rbar_locally'_filter : forall x, ProperFilter (Rbar_locally' x).
Proof.
intros [x| |] ; (constructor ; [idtac | constructor]).
- case => eps HP.
  apply (HP (x + pos eps / 2%:R)).
    rewrite /ball /= /AbsRing_ball opprD addrA subrr add0r absrN.
    rewrite !absRE normf_div !ger0_norm // ltr_pdivr_mulr //.
    by rewrite mulr_natr mulr2n ltr_addr.
  move/eqP; rewrite eq_sym addrC -subr_eq subrr => /eqP.
  by apply/eqP; rewrite ltr_eqF.
- now exists [posreal of 1].
- intros P Q [dP HP] [dQ HQ].
  exists [posreal of Num.min (pos dP) (pos dQ)] => y Hy H; split.
  + apply/(HP _ _ H)/sub_abs_ball; move/sub_ball_abs : Hy; rewrite mul1r /=.
    move/ltr_le_trans; apply; by rewrite ler_minl lerr.
  + apply/(HQ _ _ H)/sub_abs_ball; move/sub_ball_abs : Hy.
    rewrite mul1r /= => /ltr_le_trans; apply;  by rewrite ler_minl lerr orbT.
- intros P Q H [dP HP].
  exists dP => y Hy H'; by apply/H/HP.
- case=> N HP.
  apply (HP (N + 1)).
  by rewrite ltr_addl.
- now exists 0.
- intros P Q [MP HP] [MQ HQ].
  exists (Num.max MP MQ) => y Hy; split.
  + apply HP; by rewrite (ler_lt_trans _ Hy) // ler_maxr lerr.
  + apply HQ; by rewrite (ler_lt_trans _ Hy) // ler_maxr lerr orbT.
- intros P Q H [dP HP].
  exists dP => y Hy; by apply/H/HP.
- case=> N HP.
  apply (HP (N - 1)).
  by rewrite ltr_subl_addl ltr_addr.
- now exists 0.
- intros P Q [MP HP] [MQ HQ].
  exists (Num.min MP MQ) => y Hy; split.
  + apply/HP/(ltr_le_trans Hy); by rewrite ler_minl lerr.
  + apply/HQ/(ltr_le_trans Hy); by rewrite ler_minl lerr orbT.
- intros P Q H [dP HP].
  exists dP => y Hy; by apply/H/HP.
Qed.

Global Instance Rbar_locally_filter : forall x, ProperFilter (Rbar_locally x).
Proof.
case=> [x||].
by apply locally_filter.
exact (Rbar_locally'_filter +oo).
exact (Rbar_locally'_filter -oo).
Qed.

(** Open sets in [Rbar] *)

Definition open_true := @openT. (*compat*)
Definition open_false := @open0. (*compat*)
Definition closed_true := @closedT. (*compat*)
Definition closed_false := @closed0. (*compat*)

Lemma open_Rbar_lt y : open (fun u : R => Rbar_lt u y).
Proof.
case: y => [y||].
rewrite /Rbar_lt (_ : Rlt^~ y = fun x => x < y); first by eapply open_lt.
rewrite funeqE => x //; rewrite propeqE; split => [/RltP //| ?]; by apply/RltP.
by apply open_true.
by apply open_false.
Qed.

Lemma open_Rbar_gt y : open (fun u : R => Rbar_lt y u).
Proof.
case: y => [y||].
rewrite /Rbar_lt (_ : [eta Rlt y] = fun x => y < x); first by apply: open_gt.
rewrite funeqE => x //; rewrite propeqE; split => [/RltP //| ?]; by apply/RltP.
by apply open_false.
by apply open_true.
Qed.

Lemma open_Rbar_lt' x y : Rbar_lt x y -> Rbar_locally x (fun u => Rbar_lt u y).
Proof.
case: x => [x|//|] xy; first by apply open_Rbar_lt.
case: y => [y||//] in xy *.
exists y => /= x ?; by apply/RltP.
by apply filter_forall.
Qed.

Lemma open_Rbar_gt' x y : Rbar_lt y x -> Rbar_locally x (fun u => Rbar_lt y u).
Proof.
case: x => [x||] xy; first by apply open_Rbar_gt.
case: y => [y|//|] in xy *.
exists y => x yx; by apply/RltP.
by apply filter_forall.
by case: y xy.
Qed.

Lemma Rbar_locally'_le x : Rbar_locally' x --> Rbar_locally x.
Proof. by move: x => [x||] P [eps HP]; exists eps => // ???; apply: HP. Qed.

Lemma Rbar_locally'_le_finite (x : R) : Rbar_locally' x --> locally x.
Proof. by move=> P [eps HP]; exists eps => // ???; apply: HP. Qed.

(** * Some limits on real functions *)

Definition Rbar_loc_seq (x : Rbar) (n : nat) := match x with
    | Finite x => x + (INR n + 1)^-1
    | +oo => INR n
    | -oo => - INR n
  end.

Lemma filterlim_Rbar_loc_seq x : Rbar_loc_seq x --> Rbar_locally' x.
Proof.
move=> P; rewrite /Rbar_loc_seq.
case: x => /= [x | | ] [delta Hp].
- (* x \in R *)
  case: (nfloor_ex (/delta)) => [ | N [_ /RltP HN]].
    by apply Rlt_le, Rinv_0_lt_compat, delta.
  exists N => n Hn.
  apply Hp => /=.
    rewrite /ball /= /AbsRing_ball.
    rewrite INRE (_ : n%:R + _ = n.+1%:R); last by rewrite -addn1 natrD.
    rewrite opprD addrA subrr add0r absrN absRE ger0_norm //.
    rewrite -(invrK (pos delta)) ltr_pinv; last 2 first.
      by rewrite inE ltr0n andbT unitfE.
      by rewrite !inE unitfE gtr_eqF /= invr_gt0.
    move: HN; rewrite RinvE // RplusE => /ltr_le_trans; apply.
    by rewrite -addn1 natrD ler_add // INRE // ler_nat.
  move/eqP.
  rewrite eq_sym addrC -subr_eq subrr eq_sym INRE.
  rewrite (_ : n%:R + 1 = n.+1%:R); last by rewrite -addn1 natrD.
  by rewrite invr_eq0 pnatr_eq0.
- (* x = +oo *)
  case: (nfloor_ex (Num.max 0 delta)) => [ | N [_ /RltP HN]].
    by apply/RleP; rewrite ler_maxr lerr.
  exists N.+1 => n.
  rewrite -(@ler_nat [numDomainType of R]) => Hn.
  apply Hp.
  move: HN; rewrite RplusE INRE (_ : _ + 1 = N%:R + 1%:R) // -natrD addn1 => HN.
  move: (ltr_le_trans HN Hn); rewrite INRE; apply ler_lt_trans.
  by rewrite ler_maxr lerr orbT.
- (* x = -oo *)
  case: (nfloor_ex (Num.max 0 (-delta))) => [ | N [_ /RltP HN]].
    by apply/RleP; rewrite ler_maxr lerr.
  exists N.+1 => n.
  rewrite -(@ler_nat [numDomainType of R]) => Hn.
  apply Hp.
  move: HN; rewrite RplusE INRE (_ : _ + 1 = N%:R + 1%:R) // -natrD addn1 => HN.
  rewrite lter_oppl.
  move: (ltr_le_trans HN Hn); rewrite INRE; apply ler_lt_trans.
  by rewrite ler_maxr lerr orbT.
Qed.

Lemma continuity_pt_locally f x : continuity_pt f x <->
  forall eps : posreal, locally x (fun u => Rabs (f u - f x) < eps (* TODO: express using ball?*)).
Proof.
split.
- move=> H eps.
  move: (H eps (cond_pos eps)) => {H} [d [H1 H2]].
  rewrite /= /R_dist /D_x /no_cond in H2.
  exists (mkposreal _ H1) => y H.
  case/boolP: (x == y) => [/eqP <-|xy].
  + by rewrite RminusE subrr Rabs_R0.
  + apply/RltP/H2; split; [split => //; by apply/eqP|].
    by move/sub_ball_abs : H; rewrite mul1r /= absrB => /RltP.
- move=> H eps He.
  move: (H (mkposreal _ He)) => {H} [d H].
  exists d; split; first by apply cond_pos.
  move=> h [Zh Hh].
  apply/RltP/H.
  apply/(@sub_norm_ball_pos _ [normedModType R of R^o] x d)/RltP.
  by rewrite /ball_norm -normmB.
Qed.

(* COMPILES UNTIL HERE *)

Lemma continuity_pt_filterlim (f : R -> R) (x : R) :
  continuity_pt f x <-> f @ x --> f x.
Proof.
eapply iff_trans; first by apply continuity_pt_locally.
apply iff_sym.
have FF : Filter (f @ x) by typeclasses eauto.
case: (@filterlim_locally _ (f @ x) FF (f x)) => {FF}H1 H2.
(* TODO: in need for lemmas and/or refactoring of already existing lemmas (ball vs. Rabs) *)
split => [{H2} /H1{H1} H1 eps|{H1} H].
- move: (H1 eps) => {H1} [x0 Hx0].
  exists x0 => Hx0' /Hx0 /= /sub_ball_abs.
  by rewrite mul1r absrB.
- apply H2 => eps; move: (H eps) => {H} [x0 Hx0].
  exists x0 => y /Hx0 /= {Hx0}Hx0.
  apply/sub_abs_ball; by rewrite absrB.
Qed.

Lemma continuity_ptE (f : R -> R) (x : R) :
  continuity_pt f x <-> {for x, continuous f}.
Proof. exact: continuity_pt_filterlim. Qed.

Lemma continuous_withinNx {U V : uniformType} (Ueqdec : forall x y : U, x = y \/ x <> y)
  (f : U -> V) x :
  {for x, continuous f} <-> f @ locally' x --> f x.
Proof.
split=> - cfx P /= fxP.
  by rewrite /locally'; apply filter_le_within; apply/cfx.
 (* :BUG: ssr apply: does not work,
    because the type of the filter is not infered *)
have /= /filterP[//= Q Qx QP] := cfx P fxP.
apply/filterP; exists (fun y => y <> x -> Q y) => // y Qy.
by have [->|/Qy /QP //] := Ueqdec y x; apply: locally_singleton.
Qed.

Lemma continuity_pt_filterlim' f x :
  continuity_pt f x <-> f @ locally' x --> f x.
Proof. by rewrite continuity_ptE continuous_withinNx //; exact: Req_dec. Qed.

Lemma continuity_pt_locally' f x :
  continuity_pt f x <->
  forall eps : posreal, locally' x (fun u => `|f u - f x| < eps)%R.
Proof.
rewrite continuity_ptE continuous_withinNx; last exact: Req_dec.
have FF : Filter (f @ locally' x) by typeclasses eauto.
case: (@filterlim_locally _ (f @ locally' x) FF (f x)) => {FF}H1 H2.
(* TODO: refactoring  *)
split => [{H2} /H1{H1} H1 eps|{H1} H].
- move: (H1 eps) => {H1} [x0 Hx0].
  exists x0 => y /Hx0 /= H yx.
  move: (H yx) => {H yx} /sub_ball_abs.
  by rewrite mul1r absrB.
- apply H2 => eps; move: (H eps) => {H} [x0 Hx0].
  exists x0 => y /Hx0 /= {Hx0}Hx0 yx; move: (Hx0 yx) => {Hx0 yx} H.
  apply/sub_abs_ball; by rewrite absrB.
 Qed.

Lemma locally_pt_comp (P : R -> Prop) (f : R -> R) (x : R) :
  locally (f x) P -> continuity_pt f x ->
  locally x (fun x => P (f x)).
Proof.
intros Lf Cf.
apply continuity_pt_filterlim in Cf.
now apply Cf.
Qed.
