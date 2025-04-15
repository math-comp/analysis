(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra finmap all_classical.
From mathcomp Require Export filter.

(**md**************************************************************************)
(* # Basic topological notions                                                *)
(* This file develops tools for the manipulation of basic topological         *)
(* notions. The development of topological notions builds on "filtered types" *)
(* by extending the hierarchy.                                                *)
(*                                                                            *)
(* ## Mathematical structures                                                 *)
(* ### Topology                                                               *)
(* ```                                                                        *)
(*          topologicalType == interface type for topological space           *)
(*                             structure                                      *)
(*                             the HB class is Topological.                   *)
(*         ptopologicalType == a pointed topologicalType                      *)
(*                     open == set of open sets                               *)
(*                   closed == set of closed sets                             *)
(*                 clopen U == U is both open and closed                      *)
(*              open_nbhs p == set of open neighbourhoods of p                *)
(*                  basis B == a family of open sets that converges to        *)
(*                             each point                                     *)
(*       second_countable T == T has a countable basis                        *)
(*              [locally P] := forall a, A a -> G (within A (nbhs x)) if P    *)
(*                             is convertible to G (globally A)               *)
(*            finI_from D f == set of \bigcap_(i in E) f i where E is a       *)
(*                             finite subset of D                             *)
(*                       U° == all of the points which are locally in U,      *)
(*                             i.e., the largest open set contained in U      *)
(*                             This is a notation for `interior U`.           *)
(*                closure U == the smallest closed set containing U           *)
(*                regopen U == U is regular open,                             *)
(*                             i.e., equal to the interior of its closure     *)
(*              regclosed U == U is regular closed,                           *)
(*                             i.e., equal to the closure of its interior     *)
(*           open_of_nbhs B == the open sets induced by neighborhoods         *)
(*           nbhs_of_open B == the neighborhoods induced by open sets         *)
(*                      x^' == set of neighbourhoods of x where x is          *)
(*                             excluded (a "deleted neighborhood")            *)
(*            limit_point E == the set of limit points of E                   *)
(*                  dense S == the set (S : set T) is dense in T, with T of   *)
(*                             type topologicalType                           *)
(*           continuousType == type of continuous functions                   *)
(*                             The HB structures is Continuous.               *)
(*              mkcts f_cts == object of type continuousType corresponding to *)
(*                             the function f (f_cts : continuous f)          *)
(*                                                                            *)
(* ```                                                                        *)
(* ### Factories                                                              *)
(* ```                                                                        *)
(*           Nbhs_isNbhsTopological == factory for a topology defined by a    *)
(*                                     filter                                 *)
(*                                     It builds the mixin for a topological  *)
(*                                     space from the properties of nbhs and  *)
(*                                     hence assumes that the carrier is a    *)
(*                                     filterType.                            *)
(*                isOpenTopological == factory for a topology defined by open *)
(*                                     sets                                   *)
(*                                     It builds the mixin for a topological  *)
(*                                     space from the properties of open      *)
(*                                     sets, nbhs_of_open must be used to     *)
(*                                     declare a filterType.                  *)
(*                isBaseTopological == factory for a topology defined by a    *)
(*                                     base of open sets                      *)
(*                                     It builds the mixin for a topological  *)
(*                                     space from the properties of a base of *)
(*                                     open sets; the type of indices must be *)
(*                                     a pointedType                          *)
(*             isSubBaseTopological == factory for a topology defined by a    *)
(*                                     subbase of open sets                   *)
(*                                     It builds the mixin for a topological  *)
(*                                     space from a subbase of open sets b    *)
(*                                     indexed on domain D                    *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "A °" (format "A °").
Reserved Notation "[ 'locally' P ]" (format "[ 'locally'  P ]").
Reserved Notation "x ^'" (format "x ^'").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Topological spaces *)
HB.mixin Record Nbhs_isTopological (T : Type) of Nbhs T := {
  open : set_system T;
  nbhs_pfilter_subproof : forall p : T, ProperFilter (nbhs p) ;
  nbhsE_subproof : forall p : T, nbhs p =
    [set A : set T | exists B : set T, [/\ open B, B p & B `<=` A] ] ;
  openE_subproof : open = [set A : set T | A `<=` nbhs^~ A ]
}.

#[short(type="topologicalType")]
HB.structure Definition Topological :=
  {T of Nbhs T & Nbhs_isTopological T}.

#[short(type="ptopologicalType")]
HB.structure Definition PointedTopological :=
  {T of PointedNbhs T & Nbhs_isTopological T}.

#[short(type="bpTopologicalType")]
HB.structure Definition BiPointedTopological :=
  { X of BiPointed X & Topological X }.

Section Topological1.
Context {T : topologicalType}.

Definition open_nbhs (p : T) (A : set T) := open A /\ A p.

Definition basis (B : set (set T)) :=
  B `<=` open /\ forall x, filter_from [set U | B U /\ U x] id --> x.

Definition second_countable := exists2 B, countable B & basis B.

Global Instance nbhs_pfilter (p : T) : ProperFilter (nbhs p).
Proof. by apply: nbhs_pfilter_subproof; case: T p => ? []. Qed.
Typeclasses Opaque nbhs.
Lemma nbhs_filter (p : T) : Filter (nbhs p).
Proof. exact: (@nbhs_pfilter). Qed.

Canonical nbhs_filter_on (x : T) := FilterType (nbhs x) (@nbhs_filter x).

Lemma nbhsE (p : T) :
  nbhs p = [set A : set T | exists2 B : set T, open_nbhs p B & B `<=` A].
Proof.
have -> : nbhs p = [set A : set T | exists B, [/\ open B, B p & B `<=` A] ].
  exact: nbhsE_subproof.
by rewrite predeqE => A; split=> [[B [?]]|[B[]]]; exists B.
Qed.

Lemma open_nbhsE (p : T) (A : set T) : open_nbhs p A = (open A /\ nbhs p A).
Proof.
by rewrite nbhsE propeqE; split=> [[? ?]|[? [B [? ?] BA]]]; split => //;
  [exists A | exact: BA].
Qed.

Definition interior (A : set T) := (@nbhs _ T)^~ A.

Local Notation "A °" := (interior A).

Lemma interior_subset (A : set T) : A° `<=` A.
Proof.
by move=> p; rewrite /interior nbhsE => -[? [? ?]]; apply.
Qed.

Lemma openE : open = [set A : set T | A `<=` A°].
Proof. exact: openE_subproof. Qed.

Lemma nbhs_singleton (p : T) (A : set T) : nbhs p A -> A p.
Proof. by rewrite nbhsE => - [? [_ ?]]; apply. Qed.

Lemma nbhs_interior (p : T) (A : set T) : nbhs p A -> nbhs p A°.
Proof.
rewrite nbhsE /open_nbhs openE => - [B [Bop Bp] sBA].
by exists B => // q Bq; apply: filterS sBA _; apply: Bop.
Qed.

Lemma open0 : open (set0 : set T).
Proof. by rewrite openE. Qed.

Lemma openT : open (setT : set T).
Proof. by rewrite openE => ??; apply: filterT. Qed.

Lemma openI (A B : set T) : open A -> open B -> open (A `&` B).
Proof.
rewrite openE => Aop Bop p [Ap Bp].
by apply: filterI; [apply: Aop|apply: Bop].
Qed.

Lemma bigcup_open (I : Type) (D : set I) (f : I -> set T) :
  (forall i, D i -> open (f i)) -> open (\bigcup_(i in D) f i).
Proof.
rewrite openE => fop p [i Di].
by have /fop fiop := Di; move/fiop; apply: filterS => ??; exists i.
Qed.

Lemma openU (A B : set T) : open A -> open B -> open (A `|` B).
Proof.
by rewrite openE => Aop Bop p [/Aop|/Bop]; apply: filterS => ??; [left|right].
Qed.

Lemma open_subsetE (A B : set T) : open A -> (A `<=` B) = (A `<=` B°).
Proof.
rewrite openE => Aop; rewrite propeqE; split.
  by move=> sAB p Ap; apply: filterS sAB _; apply: Aop.
by move=> sAB p /sAB /interior_subset.
Qed.

Lemma open_interior (A : set T) : open A°.
Proof.
rewrite openE => p; rewrite /interior nbhsE => - [B [Bop Bp]].
by rewrite open_subsetE //; exists B.
Qed.

Lemma interior_bigcup I (D : set I) (f : I -> set T) :
  \bigcup_(i in D) (f i)° `<=` (\bigcup_(i in D) f i)°.
Proof.
move=> p [i Di]; rewrite /interior nbhsE => - [B [Bop Bp] sBfi].
by exists B => // ? /sBfi; exists i.
Qed.

Lemma open_nbhsT (p : T) : open_nbhs p setT.
Proof. by split=> //; apply: openT. Qed.

Lemma open_nbhsI (p : T) (A B : set T) :
  open_nbhs p A -> open_nbhs p B -> open_nbhs p (A `&` B).
Proof. by move=> [Aop Ap] [Bop Bp]; split; [apply: openI|split]. Qed.

Lemma open_nbhs_nbhs (p : T) (A : set T) : open_nbhs p A -> nbhs p A.
Proof. by rewrite nbhsE => p_A; exists A. Qed.

Lemma interiorI (A B : set T) : (A `&` B)° = A° `&` B°.
Proof.
rewrite /interior predeqE => //= x; rewrite nbhsE; split => [[B0 ?] | []].
- by rewrite subsetI => // -[? ?]; split; exists B0.
- by move=> -[B0 ? ?] [B1 ? ?]; exists (B0 `&` B1);
  [exact: open_nbhsI | rewrite subsetI; split; apply: subIset; [left|right]].
Qed.

End Topological1.

Lemma open_in_nearW {T : topologicalType} (P : T -> Prop) (S : set T) :
  open S -> {in S, forall x, P x} -> {in S, forall x, \near x, P x}.
Proof.
by move=> oS SP z /set_mem Sz; apply: in_nearW SP => //=; exact: open_nbhs_nbhs.
Qed.

#[global] Hint Extern 0 (Filter (nbhs _)) =>
  solve [apply: nbhs_filter] : typeclass_instances.
#[global] Hint Extern 0 (ProperFilter (nbhs _)) =>
  solve [apply: nbhs_pfilter] : typeclass_instances.

Global Instance alias_nbhs_filter {T : topologicalType} x :
  @Filter T^o (@nbhs T^o T x).
Proof. apply: @nbhs_filter T x. Qed.

Global Instance alias_nbhs_pfilter {T : topologicalType} x :
  @ProperFilter T^o (@nbhs T^o T x).
Proof. exact: @nbhs_pfilter T x. Qed.

Reserved Notation "A ^°" (at level 1, format "A ^°").
Notation "A °" := (interior A) : classical_set_scope.
#[deprecated(since="mathcomp-analysis 1.10.0", note="use the notation instead ° instead of ^°")]
Notation "A ^°" := (A°) (only parsing).

Lemma continuousP (S T : topologicalType) (f : S -> T) :
  continuous f <-> forall A, open A -> open (f @^-1` A).
Proof.
split=> fcont; first by rewrite !openE => A Aop ? /Aop /fcont.
move=> s A; rewrite nbhs_simpl /= !nbhsE => - [B [Bop Bfs] sBA].
by exists (f @^-1` B); [split=> //; apply/fcont|move=> ? /sBA].
Qed.

Lemma continuous_comp (R S T : topologicalType) (f : R -> S) (g : S -> T) x :
  {for x, continuous f} -> {for (f x), continuous g} ->
  {for x, continuous (g \o f)}.
Proof. exact: cvg_comp. Qed.

Lemma open_comp  {T U : topologicalType} (f : T -> U) (D : set U) :
  {in f @^-1` D, continuous f} -> open D -> open (f @^-1` D).
Proof.
rewrite !openE => fcont Dop x /= Dfx.
by apply: fcont; [rewrite inE|apply: Dop].
Qed.

Lemma cvg_fmap {T: topologicalType} {U : topologicalType}
  (F : set_system T) x (f : T -> U) :
   {for x, continuous f} -> F --> x -> f @ F --> f x.
Proof. by move=> cf fx P /cf /fx. Qed.

Lemma near_join (T : topologicalType) (x : T) (P : set T) :
  (\near x, P x) -> \near x, \near x, P x.
Proof. exact: nbhs_interior. Qed.

Lemma near_bind (T : topologicalType) (P Q : set T) (x : T) :
  (\near x, (\near x, P x) -> Q x) -> (\near x, P x) -> \near x, Q x.
Proof.
move=> PQ xP; near=> y; apply: (near PQ y) => //;
by apply: (near (near_join xP) y).
Unshelve. all: by end_near. Qed.

(* limit composition *)

Lemma continuous_cvg {T : Type} {V U : topologicalType}
  (F : set_system T) (FF : Filter F)
  (f : T -> V) (h : V -> U) (a : V) :
  {for a, continuous h} ->
  f @ F --> a -> (h \o f) @ F --> h a.
Proof.
move=> h_continuous fa fb; apply: (cvg_trans _ h_continuous).
exact: (@cvg_comp _ _ _ _ h _ _ _ fa).
Qed.

Lemma continuous_is_cvg {T : Type} {V U : ptopologicalType} [F : set_system T]
  (FF : Filter F) (f : T -> V) (h : V -> U) :
  (forall l, f x @[x --> F] --> l -> {for l, continuous h}) ->
  cvg (f x @[x --> F]) -> cvg ((h \o f) x @[x --> F]).
Proof.
move=> ach /cvg_ex[l fxl]; apply/cvg_ex; exists (h l).
by apply: continuous_cvg => //; exact: ach.
Qed.

Lemma continuous2_cvg {T : Type} {V W U : topologicalType}
  (F : set_system T) (FF : Filter F)
  (f : T -> V) (g : T -> W) (h : V -> W -> U) (a : V) (b : W) :
  h z.1 z.2 @[z --> (a, b)] --> h a b ->
  f @ F --> a -> g @ F --> b -> (fun x => h (f x) (g x)) @ F --> h a b.
Proof.
move=> h_continuous fa fb; apply: (cvg_trans _ h_continuous).
exact: (@cvg_comp _ _ _ _ (fun x => h x.1 x.2) _ _ _ (cvg_pair fa fb)).
Qed.

Lemma cvg_near_cst (T : Type) (U : topologicalType)
  (l : U) (f : T -> U) (F : set_system T) {FF : Filter F} :
  (\forall x \near F, f x = l) -> f @ F --> l.
Proof.
move=> fFl P /=; rewrite !near_simpl => Pl.
by apply: filterS fFl => _ ->; apply: nbhs_singleton.
Qed.
Arguments cvg_near_cst {T U} l {f F FF}.

Lemma is_cvg_near_cst (T : Type) (U : ptopologicalType)
  (l : U) (f : T -> U) (F : set_system T) {FF : Filter F} :
  (\forall x \near F, f x = l) -> cvg (f @ F).
Proof. by move=> /cvg_near_cst/cvgP. Qed.
Arguments is_cvg_near_cst {T U} l {f F FF}.

Lemma near_cst_continuous (T U : topologicalType)
  (l : U) (f : T -> U) (x : T) :
  (\forall y \near x, f y = l) -> {for x, continuous f}.
Proof.
move=> eq_f_l; apply: cvg_near_cst; apply: filterS (eq_f_l) => y ->.
by rewrite (nbhs_singleton eq_f_l).
Qed.
Arguments near_cst_continuous {T U} l [f x].

Lemma cvg_cst (U : topologicalType) (x : U) (T : Type)
    (F : set_system T) {FF : Filter F} :
  (fun _ : T => x) @ F --> x.
Proof. by apply: cvg_near_cst; near=> x0. Unshelve. all: by end_near. Qed.
Arguments cvg_cst {U} x {T F FF}.
#[global] Hint Resolve cvg_cst : core.

Lemma is_cvg_cst (U : ptopologicalType) (x : U) (T : Type)
  (F : set_system T) {FF : Filter F} :
  cvg ((fun _ : T => x) @ F).
Proof. by apply: cvgP; apply: cvg_cst. Qed.
Arguments is_cvg_cst {U} x {T F FF}.
#[global] Hint Resolve is_cvg_cst : core.

Lemma cst_continuous {T U : topologicalType} (x : U) :
  continuous (fun _ : T => x).
Proof. by move=> t; apply: cvg_cst. Qed.

Section within_topologicalType.
Context {T : topologicalType} (A : set T).
Implicit Types B : set T.

(* Relation between  globally  and  within A (nbhs x)          *)
(* to be combined with lemmas such as boundedP in normedtype.v *)
Lemma within_nbhsW (x : T) : A x -> within A (nbhs x) `=>` globally A.
Proof.
move=> Ax P AP; rewrite /within/=; near=> y; apply: AP.
Unshelve. all: by end_near. Qed.

(* [locally P] replaces a (globally A) in P by a within A (nbhs x)      *)
(* Can be combined with a notation taking a filter as its last argument *)
Definition locally_of (P : set_system T -> Prop) of phantom Prop (P (globally A))
  := forall x, A x -> P (within A (nbhs x)).
Local Notation "[ 'locally' P ]" := (@locally_of _ _ _ (Phantom _ P)).
(* e.g. [locally [bounded f x | x in A]]                  *)
(* see lemmas bounded_locally in normedtype.v for example *)

Lemma within_interior (x : T) : A° x -> within A (nbhs x) = nbhs x.
Proof.
move=> Aox; rewrite eqEsubset; split; last exact: cvg_within.
rewrite ?nbhsE => W /= => [[B + BsubW]].
rewrite open_nbhsE => [[oB nbhsB]].
exists (B `&` A°); last by move=> t /= [] /BsubW + /interior_subset; apply.
rewrite open_nbhsE; split; first by apply: openI => //; exact: open_interior.
by apply: filterI => //; have := open_interior A; rewrite openE; exact.
Qed.

Lemma within_subset B F : Filter F -> A `<=` B -> within A F `=>` within B F.
Proof.
move=> FF AsubB W; rewrite /within/=; apply: filter_app; rewrite nbhs_simpl.
by apply: filterE => ? + ?; apply; exact: AsubB.
Qed.

Lemma withinE F : Filter F ->
  within A F = [set U | exists2 V, F V & U `&` A = V `&` A].
Proof.
move=> FF; rewrite eqEsubset; split=> U.
  move=> Wu; exists [set x | A x -> U x] => //.
  by rewrite eqEsubset; split => t [L R]; split=> //; apply: L.
move=> [V FV AU]; rewrite /within /prop_near1 nbhs_simpl/=; near=> w => Aw.
by have []// : (U `&` A) w; rewrite AU; split => //; apply: (near FV).
Unshelve. all: by end_near. Qed.

Lemma fmap_within_eq {S : topologicalType} (F : set_system T) (f g : T -> S) :
  Filter F -> {in A, f =1 g} -> f @ within A F --> g @ within A F.
Proof.
move=> FF feq U /=; near_simpl; apply: filter_app.
rewrite ?nbhs_simpl; near_simpl; near=> w; rewrite (feq w) // inE.
exact: (near (withinT A FF) w).
Unshelve. all: by end_near. Qed.

End within_topologicalType.

Notation "[ 'locally' P ]" := (@locally_of _ _ _ (Phantom _ P)).

(** Topology defined by a filter *)

HB.factory Record Nbhs_isNbhsTopological T of Nbhs T := {
  nbhs_filter : forall p : T, ProperFilter (nbhs p);
  nbhs_singleton : forall (p : T) (A : set T), nbhs p A -> A p;
  nbhs_nbhs : forall (p : T) (A : set T), nbhs p A -> nbhs p (nbhs^~ A);
}.

HB.builders Context T of Nbhs_isNbhsTopological T.

Definition open_of_nbhs := [set A : set T | A `<=` nbhs^~ A].

Let nbhsE_subproof (p : T) :
  nbhs p = [set A | exists B, [/\ open_of_nbhs B, B p & B `<=` A] ].
Proof.
rewrite predeqE => A; split=> [p_A|]; last first.
  move=> [B [Bop Bp sBA]]; apply: filterS sBA _; last exact: Bop.
  exact/nbhs_filter.
exists (nbhs^~ A); split=> //; first by move=> ?; apply: nbhs_nbhs.
by move=> q /nbhs_singleton.
Qed.

Let openE_subproof : open_of_nbhs = [set A : set T | A `<=` nbhs^~ A].
Proof. by []. Qed.

HB.instance Definition _ := Nbhs_isTopological.Build T
  nbhs_filter nbhsE_subproof openE_subproof.

HB.end.

(** Topology defined by open sets *)

Definition nbhs_of_open (T : Type) (op : set T -> Prop) (p : T) (A : set T) :=
  exists B, [/\ op B, B p & B `<=` A].

HB.factory Record isOpenTopological T of Choice T := {
  op : set T -> Prop;
  opT : op setT;
  opI : forall (A B : set T), op A -> op B -> op (A `&` B);
  op_bigU : forall (I : Type) (f : I -> set T), (forall i, op (f i)) ->
    op (\bigcup_i f i);
}.

HB.builders Context T of isOpenTopological T.

HB.instance Definition _ := hasNbhs.Build T (nbhs_of_open op).

Let nbhs_pfilter_subproof (p : T) : ProperFilter (nbhs p).
Proof.
apply: Build_ProperFilter_ex.
  by move=> A [B [_ Bp sBA]]; exists p; apply: sBA.
split; first by exists setT; split=> [|//|//]; exact: opT.
  move=> A B [C [Cop Cp sCA]] [D [Dop Dp sDB]].
  exists (C `&` D); split=> //; first exact: opI.
  by move=> q [/sCA Aq /sDB Bq].
move=> A B sAB [C [Cop p_C sCA]].
by exists C; split=> //; apply: subset_trans sAB.
Qed.

Let nbhsE_subproof (p : T) :
  nbhs p = [set A | exists B, [/\ op B, B p & B `<=` A] ].
Proof. by []. Qed.

Let openE_subproof : op = [set A : set T | A `<=` nbhs^~ A].
Proof.
rewrite predeqE => A; split=> [Aop p Ap|Aop].
  by exists A; split=> //; split.
suff -> : A = \bigcup_(B : {B : set T & op B /\ B `<=` A}) projT1 B.
  by apply: op_bigU => B; have [] := projT2 B.
rewrite predeqE => p; split=> [|[B _ Bp]]; last by have [_] := projT2 B; apply.
by move=> /Aop [B [Bop Bp sBA]]; exists (existT _ B (conj Bop sBA)).
Qed.

HB.instance Definition _ := Nbhs_isTopological.Build T
  nbhs_pfilter_subproof nbhsE_subproof openE_subproof.

HB.end.

(** Topology defined by a base of open sets *)

HB.factory Record isBaseTopological T of Choice T := {
  I : pointedType;
  D : set I;
  b : I -> (set T);
  b_cover : \bigcup_(i in D) b i = setT;
  b_join : forall i j t, D i -> D j -> b i t -> b j t ->
    exists k, [/\ D k, b k t & b k `<=` b i `&` b j];
}.

HB.builders Context T of isBaseTopological T.

Definition open_from := [set \bigcup_(i in D') b i | D' in subset^~ D].

Let open_fromT : open_from setT.
Proof. exists D => //; exact: b_cover. Qed.

Let open_fromI (A B : set T) : open_from A -> open_from B ->
  open_from (A `&` B).
Proof.
move=> [DA sDAD AeUbA] [DB sDBD BeUbB].
have ABU : forall t, (A `&` B) t ->
  exists it, D it /\ b it t /\ b it `<=` A `&` B.
  move=> t [At Bt].
  have [iA [DiA [biAt sbiA]]] : exists i, D i /\ b i t /\ b i `<=` A.
    move: At; rewrite -AeUbA => - [i DAi bit]; exists i.
    by split; [apply: sDAD|split=> // ?; exists i].
  have [iB [DiB [biBt sbiB]]] : exists i, D i /\ b i t /\ b i `<=` B.
    move: Bt; rewrite -BeUbB => - [i DBi bit]; exists i.
    by split; [apply: sDBD|split=> // ?; exists i].
  have [i [Di bit sbiAB]] := b_join DiA DiB biAt biBt.
  by exists i; split=> //; split=> // s /sbiAB [/sbiA ? /sbiB].
set Dt := fun t => [set it | D it /\ b it t /\ b it `<=` A `&` B].
exists [set get (Dt t) | t in A `&` B].
  by move=> _ [t ABt <-]; have /ABU/getPex [] := ABt.
rewrite predeqE => t; split=> [[_ [s ABs <-] bDtst]|ABt].
  by have /ABU/getPex [_ [_]] := ABs; apply.
by exists (get (Dt t)); [exists t| have /ABU/getPex [? []]:= ABt].
Qed.

Let open_from_bigU (I0 : Type) (f : I0 -> set T) :
  (forall i, open_from (f i)) -> open_from (\bigcup_i f i).
Proof.
set fop := fun j => [set Dj | Dj `<=` D /\ f j = \bigcup_(i in Dj) b i].
exists (\bigcup_j get (fop j)).
  move=> i [j _ fopji].
  suff /getPex [/(_ _ fopji)] : exists Dj, fop j Dj by [].
  by have [Dj] := H j; exists Dj.
rewrite predeqE => t; split=> [[i [j _ fopji bit]]|[j _]].
  exists j => //; suff /getPex [_ ->] : exists Dj, fop j Dj by exists i.
  by have [Dj] := H j; exists Dj.
have /getPex [_ ->] : exists Dj, fop j Dj by have [Dj] := H j; exists Dj.
by move=> [i]; exists i => //; exists j.
Qed.

HB.instance Definition _ := isOpenTopological.Build T
  open_fromT open_fromI open_from_bigU.

HB.end.

HB.factory Record isSubBaseTopological T of Choice T := {
  I : pointedType;
  D : set I;
  b : I -> (set T);
}.

HB.builders Context T of isSubBaseTopological T.

Local Notation finI_from := (finI_from D b).

Let finI_from_cover : \bigcup_(A in finI_from) A = setT.
Proof.
rewrite predeqE => t; split=> // _; exists setT => //.
by exists fset0 => //; rewrite predeqE.
Qed.

Let finI_from_join A B t : finI_from A -> finI_from B -> A t -> B t ->
  exists k, [/\ finI_from k, k t & k `<=` A `&` B].
Proof.
move=> [DA sDAD AeIbA] [DB sDBD BeIbB] At Bt.
exists (A `&` B); split => //.
exists (DA `|` DB)%fset; first by move=> i /fsetUP [/sDAD|/sDBD].
rewrite predeqE => s; split=> [Ifs|[As Bs] i /fsetUP].
  split; first by rewrite -AeIbA => i DAi; apply: Ifs; rewrite /= inE DAi.
  by rewrite -BeIbB => i DBi; apply: Ifs; rewrite /= inE DBi orbC.
by move=> [DAi|DBi];
  [have := As; rewrite -AeIbA; apply|have := Bs; rewrite -BeIbB; apply].
Qed.

HB.instance Definition _ := isBaseTopological.Build T
  finI_from_cover finI_from_join.

HB.end.

(** deleted neighborhood *)

Definition dnbhs {T : topologicalType} (x : T) :=
  within (fun y => y != x) (nbhs x).
Notation "x ^'" := (dnbhs x) : classical_set_scope.

Lemma nbhs_dnbhs_neq {T : topologicalType} (p : T) :
  \forall x \near nbhs p^', x != p.
Proof. exact: withinT. Qed.

Lemma dnbhsE (T : topologicalType) (x : T) : nbhs x = x^' `&` at_point x.
Proof.
rewrite predeqE => A; split=> [x_A|[x_A Ax]].
  split; last exact: nbhs_singleton.
  move: x_A; rewrite nbhsE => -[B [oB x_B sBA]]; rewrite /dnbhs nbhsE.
  by exists B => // ? /sBA.
move: x_A; rewrite /dnbhs !nbhsE => -[B [oB x_B sBA]]; exists B => //.
by move=> y /sBA Ay; case: (eqVneq y x) => [->|].
Qed.

Global Instance dnbhs_filter {T : topologicalType} (x : T) : Filter x^'.
Proof. exact: within_filter. Qed.
#[global] Typeclasses Opaque dnbhs.

Canonical dnbhs_filter_on (T : topologicalType)  (x : T) :=
  FilterType x^' (dnbhs_filter _).

Lemma cvg_fmap2 (T U : Type) (f : T -> U):
  forall (F G : set_system T), G `=>` F -> f @ G `=>` f @ F.
Proof. by move=> F G H A fFA ; exact: H (preimage f A) fFA. Qed.

Lemma cvg_within_filter {T U} {f : T -> U} (F : set_system T) {FF : (Filter F) }
  (G : set_system U) : forall (D : set T), (f @ F) --> G -> (f @ within D F) --> G.
Proof. move=> ?;  exact: cvg_trans (cvg_fmap2 (cvg_within _)). Qed.

Lemma cvg_app_within {T} {U : ptopologicalType} (f : T -> U) (F : set_system T)
  (D : set T): Filter F -> cvg (f @ F) -> cvg (f @ within D F).
Proof. by move => FF /cvg_ex [l H]; apply/cvg_ex; exists l; exact: cvg_within_filter. Qed.

Lemma nbhs_dnbhs {T : topologicalType} (x : T) : x^' `=>` nbhs x.
Proof. exact: cvg_within. Qed.

(** meets *)

Lemma meets_openr {T : topologicalType} (F : set_system T) (x : T) :
  F `#` nbhs x = F `#` open_nbhs x.
Proof.
rewrite propeqE; split; [exact/meetsSr/open_nbhs_nbhs|].
by move=> P A B {}/P P; rewrite nbhsE => -[B' /P + sB]; apply: subsetI_neq0.
Qed.

Lemma meets_openl {T : topologicalType} (F : set_system T) (x : T) :
  nbhs x `#` F = open_nbhs x `#` F.
Proof. by rewrite meetsC meets_openr meetsC. Qed.
(** Closed sets in topological spaces *)

Section Closed.

Context {T : topologicalType}.

Definition closure (A : set T) :=
  [set p : T | forall B, nbhs p B -> A `&` B !=set0].

Lemma closureEnbhs A : closure A = [set p | globally A `#` nbhs p].
Proof. by under eq_fun do rewrite meets_globallyl. Qed.

Lemma closureEonbhs A : closure A = [set p | globally A `#` open_nbhs p].
Proof. by under eq_fun do rewrite -meets_openr meets_globallyl. Qed.

Lemma subset_closure (A : set T) : A `<=` closure A.
Proof. by move=> p ??; exists p; split=> //; apply: nbhs_singleton. Qed.

Lemma closure_eq0 (A : set T) : closure A = set0 -> A = set0.
Proof.
by move=> A0; apply/seteqP; split => //; rewrite -A0; exact: subset_closure.
Qed.

Lemma closureI (A B : set T) : closure (A `&` B) `<=` closure A `&` closure B.
Proof. by move=> p clABp; split=> ? /clABp [q [[]]]; exists q. Qed.

Definition limit_point E := [set t : T |
  forall U, nbhs t U -> exists y, [/\ y != t, E y & U y]].

Lemma limit_pointEnbhs E :
  limit_point E = [set p | globally (E `\ p) `#` nbhs p].
Proof.
under eq_fun do rewrite meets_globallyl; rewrite funeqE => p /=.
apply/eq2_forall => x px; apply/eq_exists => y.
by rewrite propeqE; split => [[/eqP ? ?]|[[? /eqP ?]]]; do 2?split.
Qed.

Lemma limit_pointEonbhs E :
  limit_point E = [set p | globally (E `\ p) `#` open_nbhs p].
Proof. by rewrite limit_pointEnbhs; under eq_fun do rewrite meets_openr. Qed.

Lemma subset_limit_point E : limit_point E `<=` closure E.
Proof. by move=> t Et U tU; have [p [? ? ?]] := Et _ tU; exists p. Qed.

Lemma closure_limit_point E : closure E = E `|` limit_point E.
Proof.
rewrite predeqE => t; split => [cEt|]; last first.
  by case; [exact: subset_closure|exact: subset_limit_point].
have [?|Et] := pselect (E t); [by left|right=> U tU; have [p []] := cEt _ tU].
by exists p; split => //; apply/eqP => pt; apply: Et; rewrite -pt.
Qed.

Definition closed (D : set T) := closure D `<=` D.

Lemma open_closedC (D : set T) : open D -> closed (~` D).
Proof. by rewrite openE => Dop p clNDp /Dop /clNDp [? []]. Qed.

Lemma closed_bigI {I} (D : set I) (f : I -> set T) :
  (forall i, D i -> closed (f i)) -> closed (\bigcap_(i in D) f i).
Proof.
move=> fcl t clft i Di; have /fcl := Di; apply.
by move=> A /clft [s [/(_ i Di)]]; exists s.
Qed.

Lemma closedI (D E : set T) : closed D -> closed E -> closed (D `&` E).
Proof.
by move=> Dcl Ecl p clDEp; split; [apply: Dcl|apply: Ecl];
  move=> A /clDEp [q [[]]]; exists q.
Qed.

Lemma closedT : closed setT. Proof. by []. Qed.

Lemma closed0 : closed set0.
Proof. by move=> ? /(_ setT) [|? []] //; apply: filterT. Qed.

Lemma closedE : closed = [set A : set T | forall p, ~ (\near p, ~ A p) -> A p].
Proof.
rewrite predeqE => A; split=> Acl p; last first.
  by move=> clAp; apply: Acl; rewrite -nbhs_nearE => /clAp [? []].
rewrite -nbhs_nearE nbhsE => /asboolP.
rewrite asbool_neg => /forallp_asboolPn2 clAp.
apply: Acl => B; rewrite nbhsE => - [C [oC pC]].
have /asboolP := clAp C.
rewrite asbool_or 2!asbool_neg => /orP[/asboolP/not_andP[]//|/existsp_asboolPn [q]].
move/asboolP; rewrite asbool_neg => /imply_asboolPn[+ /contrapT Aq sCB] => /sCB.
by exists q.
Qed.

Lemma closed_openC (D : set T) : closed D -> open (~` D).
Proof.
rewrite closedE openE => Dcl t nDt; apply: contrapT.
by rewrite /interior nbhs_nearE => /Dcl.
Qed.

Lemma closedC (D : set T) : closed (~` D) = open D.
Proof.
by apply/propext; split=> [/closed_openC|]; [rewrite setCK|exact: open_closedC].
Qed.

Lemma openC (D : set T) : open (~`D) = closed (D).
Proof. by rewrite -closedC setCK. Qed.

Lemma closed_closure (A : set T) : closed (closure A).
Proof. by move=> p clclAp B /nbhs_interior /clclAp [q [clAq /clAq]]. Qed.

End Closed.

Lemma closed_comp {T U : topologicalType} (f : T -> U) (D : set U) :
  {in ~` f @^-1` D, continuous f} -> closed D -> closed (f @^-1` D).
Proof.
rewrite !closedE=> f_continuous D_cl x /= xDf.
apply: D_cl; apply: contra_not xDf => fxD.
have NDfx : ~ D (f x).
  by move: fxD; rewrite -nbhs_nearE nbhsE => - [A [? ?]]; apply.
by apply: f_continuous fxD; rewrite inE.
Qed.

Lemma closed_cvg {T} {V : topologicalType} {F} {FF : ProperFilter F}
    (u_ : T -> V) (A : V -> Prop) :
    (* BUG: elim does not see this as an elimination principle if A : set V *)
    closed A -> (\forall n \near F, A (u_ n)) ->
  forall l, u_ @ F --> l -> A l.
Proof.
move=> + FAu_ l u_Fl; apply => B /u_Fl /=; rewrite nbhs_filterE.
by move=> /(filterI FAu_) => /filter_ex[t [Au_t u_Bt]]; exists (u_ t).
Qed.
Arguments closed_cvg {T V F FF u_} _ _ _ _ _.

Lemma continuous_closedP (S T : topologicalType) (f : S -> T) :
  continuous f <-> forall A, closed A -> closed (f @^-1` A).
Proof.
rewrite continuousP; split=> ctsf ? ?.
  by rewrite -openC preimage_setC; apply: ctsf; rewrite openC.
by rewrite -closedC preimage_setC; apply: ctsf; rewrite closedC.
Qed.

Lemma closedU (T : topologicalType) (D E : set T) :
  closed D -> closed E -> closed (D `|` E).
Proof. by rewrite -?openC setCU; exact: openI. Qed.

Lemma closed_bigsetU (T : topologicalType) (I : eqType) (s : seq I)
    (F : I -> set T) : (forall x, x \in s -> closed (F x)) ->
  closed (\big[setU/set0]_(x <- s) F x).
Proof.
move=> scF; rewrite big_seq.
by elim/big_ind : _ => //; [exact: closed0|exact: closedU].
Qed.

Lemma closed_bigcup (T : topologicalType) (I : choiceType) (A : set I)
    (F : I -> set T) :
    finite_set A -> (forall i, A i -> closed (F i)) ->
  closed (\bigcup_(i in A) F i).
Proof.
move=> finA cF; rewrite -bigsetU_fset_set//; apply: closed_bigsetU => i.
by rewrite in_fset_set// inE; exact: cF.
Qed.

Section closure_lemmas.
Variable T : topologicalType.
Implicit Types E A B U : set T.

Lemma closure_subset A B : A `<=` B -> closure A `<=` closure B.
Proof. by move=> ? ? CAx ?; move/CAx; exact/subsetI_neq0. Qed.

Lemma closureE A : closure A = smallest closed A.
Proof.
rewrite eqEsubset; split=> [x ? B [cB AB]|]; first exact/cB/(closure_subset AB).
exact: (smallest_sub (@closed_closure _ _) (@subset_closure _ _)).
Qed.

(* TODO: the LHS and RHS of the equality should be swapped *)
Lemma closure_id E : closed E <-> E = closure E.
Proof.
split=> [?|->]; last exact: closed_closure.
rewrite eqEsubset; split => //; exact: subset_closure.
Qed.

End closure_lemmas.

Section regular_open_closed.
Variable T : topologicalType.

Definition regopen (A : set T) := (closure A)° = A.

Definition regclosed (A : set T) := closure (A°) = A.

End regular_open_closed.

Section closure_interior_lemmas.
Variable T : topologicalType.
Implicit Types (A B : set T).

Lemma interiorC A : (~` A)° = ~` closure A.
Proof.
rewrite eqEsubset; split=> x; rewrite /closure /interior nbhsE /= -existsNE.
  case=> U ? /disjoints_subset UA; exists U; rewrite not_implyE.
  split; first exact/open_nbhs_nbhs.
  by rewrite setIC UA; apply/set0P; rewrite eqxx.
case=> X; rewrite not_implyE nbhsE=> -[] -[] U xU UX AX0.
exists U => //; apply/(subset_trans UX)/disjoints_subset; rewrite setIC.
exact/eqP/negbNE/negP/set0P.
Qed.

(* TODO: rename to closureC after removing the deprecated one *)
Lemma closure_setC A : closure (~` A) = ~` A°.
Proof. by apply: setC_inj; rewrite -interiorC !setCK. Qed.

Lemma interior_id A : open A <-> interior A = A.
Proof.
by rewrite -(setCK A) openC interiorC closure_id; split => [ <- | /setC_inj->].
Qed.

Lemma closureT : closure [set: T] = [set: T].
Proof. exact/esym/closure_id/closedT. Qed.

Lemma closure0 : closure (@set0 T) = set0.
Proof. exact/esym/closure_id/closed0. Qed.

Lemma interiorT : (@setT T)° = setT.
Proof. exact/interior_id/openT. Qed.

Lemma interior0 : (@set0 T)° = set0.
Proof. exact/interior_id/open0. Qed.

Lemma closureU A B : closure (A `|` B) = closure A `|` closure B.
Proof. by apply: setC_inj; rewrite setCU -!interiorC -interiorI setCU. Qed.

Lemma interiorU A B : A° `|` B° `<=` (A `|` B)°.
Proof.
by apply: subsetC2; rewrite setCU -!closure_setC setCU; exact: closureI.
Qed.

Lemma closureEbigcap A :
  closure A = \bigcap_(x in [set C | closed C /\ A `<=` C]) x.
Proof. exact: closureE. Qed.

Lemma interiorEbigcup A :
  A° = \bigcup_(x in [set U | open U /\ U `<=` A]) x.
Proof.
apply: setC_inj; rewrite -closure_setC closureEbigcap setC_bigcup.
rewrite -[RHS](bigcap_image _ setC idfun) /=.
apply: eq_bigcapl; split => X /=.
  by rewrite -openC -setCS setCK; exists (~` X)=> //; rewrite setCK.
by case=> Y + <-; rewrite closedC setCS.
Qed.

Lemma interior_closed_regopen A : closed A -> regopen A°.
Proof.
move=> cA; rewrite /regopen eqEsubset; split=> x.
  rewrite /closure [X in X -> _]/interior nbhsE => -[] U oxU UciA.
  rewrite /interior nbhsE /=; exists U => //.
  apply: (subset_trans UciA) => y /= yA.
  apply: cA => B /yA; apply/subset_nonempty; apply: setSI.
  exact: interior_subset.
rewrite {1}/interior nbhsE=> -[] U [] oU Ux UA.
rewrite {1}/interior nbhsE /=; exists U=> //.
have:= UA; rewrite open_subsetE// => /subset_trans; apply.
exact: subset_closure.
Qed.

Lemma closure_open_regclosed A : open A -> regclosed (closure A).
Proof.
rewrite /regclosed -(setCK A) openC => cCA.
rewrite closure_setC -[in RHS]interior_closed_regopen//.
by rewrite !(closure_setC, interiorC).
Qed.

Lemma interior_closure_idem : @idempotent_fun (set T) (interior \o closure).
Proof. move=> ?; exact/interior_closed_regopen/closed_closure. Qed.

Lemma closure_interior_idem : @idempotent_fun (set T) (closure \o interior).
Proof. move=> ?; exact/closure_open_regclosed/open_interior. Qed.

End closure_interior_lemmas.

Lemma closureC_deprecated (T : topologicalType) (E : set T) :
  ~` closure E = \bigcup_(x in [set U | open U /\ U `<=` ~` E]) x.
Proof. by rewrite -interiorC interiorEbigcup. Qed.
#[deprecated(since="mathcomp-analysis 1.7.0", note="use `interiorC` and `interiorEbigcup` instead")]
Notation closureC := closureC_deprecated (only parsing).

Definition dense (T : topologicalType) (S : set T) :=
  forall (O : set T), O !=set0 -> open O -> O `&` S !=set0.

Lemma denseNE (T : topologicalType) (S : set T) : ~ dense S ->
  exists O, (exists x, open_nbhs x O) /\ (O `&` S = set0).
Proof.
rewrite /dense /open_nbhs.
move=> /existsNP[X /not_implyP[[x Xx] /not_implyP[ Ox /forallNP A]]].
by exists X; split; [exists x | rewrite -subset0; apply/A].
Qed.

Section ClopenSets.
Implicit Type T : topologicalType.

Definition clopen {T} (A : set T) := open A /\ closed A.

Lemma clopenI {T} (A B : set T) : clopen A -> clopen B -> clopen (A `&` B).
Proof. by case=> ? ? [] ? ?; split; [exact: openI | exact: closedI]. Qed.

Lemma clopenU {T} (A B : set T) : clopen A -> clopen B -> clopen (A `|` B).
Proof. by case=> ? ? [] ? ?; split; [exact: openU | exact: closedU]. Qed.

Lemma clopenC {T} (A B : set T) : clopen A -> clopen (~`A).
Proof. by case=> ? ?; split;[exact: closed_openC | exact: open_closedC ]. Qed.

Lemma clopen0 {T} : @clopen T set0.
Proof. by split; [exact: open0 | exact: closed0]. Qed.

Lemma clopenT {T} : clopen [set: T].
Proof. by split; [exact: openT | exact: closedT]. Qed.

Lemma clopen_comp {T U : topologicalType} (f : T -> U) (A : set U) :
 clopen A -> continuous f -> clopen (f @^-1` A).
Proof. by case=> ? ?; split; [ exact: open_comp | exact: closed_comp]. Qed.

End ClopenSets.

HB.mixin Record isContinuous {X Y : nbhsType} (f : X -> Y):= {
  cts_fun : continuous f
}.

#[short(type = "continuousType")]
HB.structure Definition Continuous {X Y : nbhsType} := {
  f of @isContinuous X Y f
}.

HB.instance Definition _ {X Y : topologicalType} :=
  gen_eqMixin (continuousType X Y).
HB.instance Definition _ {X Y : topologicalType} :=
  gen_choiceMixin (continuousType X Y).

Lemma continuousEP {X Y : nbhsType} (f g : continuousType X Y) :
  f = g <-> f =1 g.
Proof.
case: f g => [f [[ffun]]] [g [[gfun]]]/=; split=> [[->//]|/funext eqfg].
rewrite eqfg in ffun *; congr {| Continuous.sort := _; Continuous.class := {|
  Continuous.topology_structure_isContinuous_mixin :=
    {|isContinuous.cts_fun := _|}|}|}.
exact: Prop_irrelevance.
Qed.

Definition mkcts {X Y : nbhsType} (f : X -> Y) (f_cts : continuous f) := f.

HB.instance Definition _ {X Y : nbhsType} (f: X -> Y) (f_cts : continuous f) :=
  @isContinuous.Build X Y (mkcts f_cts) f_cts.

Section continuous_comp.
Context {X Y Z : topologicalType}.
Context (f : continuousType X Y) (g : continuousType Y Z).

Local Lemma cts_fun_comp : continuous (g \o f).
Proof. move=> x; apply: continuous_comp; exact: cts_fun. Qed.

HB.instance Definition _ := @isContinuous.Build X Z (g \o f) cts_fun_comp.

End continuous_comp.

Section continuous_id.
Context {X : topologicalType}.

Local Lemma cts_id : continuous (@idfun X).
Proof. by move=> ?. Qed.

HB.instance Definition _ := @isContinuous.Build X X (@idfun X) cts_id.

End continuous_id.

Section continuous_const.
Context {X Y : topologicalType} (y : Y).

Local Lemma cts_const : continuous (@cst X Y y).
Proof. by move=> ?; exact: cvg_cst. Qed.

HB.instance Definition _ := @isContinuous.Build X Y (cst y) cts_const.

End continuous_const.
