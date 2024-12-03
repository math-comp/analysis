(* mathcomp analysis (c) 2024 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra finmap generic_quotient.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop reals signed topology.
From mathcomp Require Import function_spaces separation_axioms.
From mathcomp Require Import wedge_sigT.

(**md**************************************************************************)
(* # Paths                                                                    *)
(* Paths from biPointed spaces.                                               *)
(*                                                                            *)
(* ```                                                                        *)
(*    mk_path ctsf f0 f1 == constructs a value in `pathType x y` given proofs *)
(*                          that the endpoints of `f` are `x` and `y`         *)
(*  reparameterize f phi == the path `f` with a different parameterization    *)
(*        chain_path f g == the path which follows f, then follows g          *)
(*                          Only makes sense when `f one = g zero`. The       *)
(*                          domain is the wedge of domains of `f` and `g`.    *)
(* ```                                                                        *)
(* The type `{path i from x to y in T}` is the continuous functions on the    *)
(* bipointed space i that go from x to y staying in T. It is endowed with     *)
(* - Topology via the compact-open topology                                   *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "{ 'path' i 'from' x 'to' y }" (
  at level 0, i at level 69, x at level 69, y at level 69,
  only parsing,
  format "{ 'path'  i  'from'  x  'to'  y }").
Reserved Notation "{ 'path' i 'from' x 'to' y 'in' T }" (
  at level 0, i at level 69, x at level 69, y at level 69, T at level 69,
  format "{ 'path'  i  'from'  x  'to'  y  'in'  T }").

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope quotient_scope.

HB.mixin Record isPath {i : bpTopologicalType} {T : topologicalType} (x y : T)
    (f : i -> T) of isContinuous i T f := {
  path_zero : f zero = x;
  path_one : f one = y;
}.

#[short(type="pathType")]
HB.structure Definition Path {i : bpTopologicalType} {T : topologicalType}
  (x y : T) := {f of isPath i T x y f & isContinuous i T f}.

Notation "{ 'path' i 'from' x 'to' y }" := (pathType i x y) : type_scope.
Notation "{ 'path' i 'from' x 'to' y 'in' T }" :=
  (@pathType i T x y) : type_scope.

HB.instance Definition _ {i : bpTopologicalType}
  {T : topologicalType} (x y : T) := gen_eqMixin {path i from x to y}.
HB.instance Definition _ {i : bpTopologicalType}
  {T : topologicalType} (x y : T) := gen_choiceMixin {path i from x to y}.
HB.instance Definition _ {i : bpTopologicalType}
    {T : topologicalType} (x y : T) :=
  Topological.copy {path i from x to y}
    (@weak_topology {path i from x to y} {compact-open, i -> T} id).

Section path_eq.
Context {T : topologicalType} {i : bpTopologicalType} (x y : T).

Lemma path_eqP (a b : {path i from x to y}) : a = b <-> a =1 b.
Proof.
split=> [->//|].
move: a b => [/= f [[+ +]]] [/= g [[+ +]]] fgE.
move/funext : fgE => -> /= a1 [b1 c1] a2 [b2 c2]; congr (_ _).
rewrite (Prop_irrelevance a1 a2) (Prop_irrelevance b1 b2).
by rewrite (Prop_irrelevance c1 c2).
Qed.

End path_eq.

Section cst_path.
Context {T : topologicalType} {i : bpTopologicalType} (x: T).

HB.instance Definition _ := @isPath.Build i T x x (cst x) erefl erefl.
End cst_path.

Section path_domain_path.
Context {i : bpTopologicalType}.
HB.instance Definition _ := @isPath.Build i i zero one idfun erefl erefl.
End path_domain_path.

Section path_compose.
Context {T U : topologicalType} (i: bpTopologicalType) (x y : T).
Context (f : continuousType T U) (p : {path i from x to y}).

Local Lemma fp_zero : (f \o p) zero = f x.
Proof. by rewrite /= !path_zero. Qed.

Local Lemma fp_one : (f \o p) one = f y.
Proof. by rewrite /= !path_one. Qed.

HB.instance Definition _ := isPath.Build i U (f x) (f y) (f \o p)
  fp_zero fp_one.

End path_compose.

Section path_reparameterize.
Context {T : topologicalType} (i j: bpTopologicalType) (x y : T).
Context (f : {path i from x to y}) (phi : {path j from zero to one in i}).

(* we use reparameterize, as opposed to just `\o` because we can simplify the
   endpoints. So we don't end up with `f \o p : {path j from f zero to f one}`
   but rather `{path j from zero to one}`
*)
Definition reparameterize := f \o phi.

Local Lemma fphi_zero : reparameterize zero = x.
Proof. by rewrite /reparameterize /= ?path_zero. Qed.

Local Lemma fphi_one : reparameterize one = y.
Proof. by rewrite /reparameterize /= ?path_one. Qed.

Local Lemma fphi_cts : continuous reparameterize.
Proof. by move=> ?; apply: continuous_comp; apply: cts_fun. Qed.

HB.instance Definition _ := isContinuous.Build _ _ reparameterize fphi_cts.

HB.instance Definition _ := isPath.Build j T x y reparameterize
  fphi_zero fphi_one.

End path_reparameterize.

Section mk_path.
Context {i : bpTopologicalType} {T : topologicalType}.
Context {x y : T} (f : i -> T) (ctsf : continuous f).
Context (f0 : f zero = x) (f1 : f one = y).

Definition mk_path : i -> T := let _ := (ctsf, f0, f1) in f.

HB.instance Definition _ := isContinuous.Build i T mk_path ctsf.
HB.instance Definition _ := @isPath.Build i T x y mk_path f0 f1.
End mk_path.

Definition chain_path {i j : bpTopologicalType} {T : topologicalType}
    (f : i -> T) (g : j -> T) : bpwedge i j -> T :=
  wedge_fun (fun b => if b return (if b then i else j) -> T then f else g).

Lemma chain_path_cts_point {i j : bpTopologicalType} {T : topologicalType}
    (f : i -> T) (g : j -> T) :
  continuous f ->
  continuous g ->
  f one = g zero ->
  continuous (chain_path f g).
Proof. by move=> cf cg fgE; apply: wedge_fun_continuous => // [[]|[] []]. Qed.

Section chain_path.
Context {T : topologicalType} {i j : bpTopologicalType} (x y z: T).
Context (p : {path i from x to y}) (q : {path j from y to z}).

Local Lemma chain_path_zero : chain_path p q zero = x.
Proof.
rewrite /chain_path /= wedge_lift_funE ?path_one ?path_zero //.
by case => //= [][] //=; rewrite ?path_one ?path_zero.
Qed.

Local Lemma chain_path_one : chain_path p q one = z.
Proof.
rewrite /chain_path /= wedge_lift_funE ?path_zero ?path_one //.
by case => //= [][] //=; rewrite ?path_one ?path_zero.
Qed.

Local Lemma chain_path_cts : continuous (chain_path p q).
Proof.
apply: chain_path_cts_point; [exact: cts_fun..|].
by rewrite path_zero path_one.
Qed.

HB.instance Definition _ :=  @isContinuous.Build _ T (chain_path p q)
  chain_path_cts.
HB.instance Definition _ :=  @isPath.Build _ T x z (chain_path p q)
  chain_path_zero chain_path_one.

End chain_path.

(* Such a structure is very much like [a,b] in that
   one can split it in half like `[0,1] \/ [0,1] ~ [0,2] ~ [0,1]
*)
HB.mixin Record isSelfSplit (X : Type) of BiPointedTopological X := {
  to_wedge  : {path X from zero to one in bpwedge X X };
  to_wedge_bij : bijective to_wedge;
  to_wedge_cts : continuous to_wedge;
  to_wedge_open : forall A, open A -> open (to_wedge @` A);
}.

#[short(type="selfSplitType")]
HB.structure Definition SelfSplit := {
  X of BiPointedTopological X & isSelfSplit X
}.

Section path_concat.
Context {T : topologicalType} {i : selfSplitType} (x y z: T).
Context (p : {path i from x to y}) (q : {path i from y to z}).

Definition path_concat : {path i from x to z} :=
  reparameterize (chain_path p q) (to_wedge).

End path_concat.

Section self_wedge_path.
Context {i : selfSplitType}.

Definition from_wedge_sub : bpwedge i i -> i  := 
  ((bijection_of_bijective (@to_wedge_bij i))^-1)%FUN.

Local Lemma from_wedge_zero : from_wedge_sub zero = zero.
Proof.
move/bij_inj : (@to_wedge_bij i); apply.
rewrite /from_wedge_sub /=. 
have /= -> := (@invK _ _ _ _ (bijection_of_bijective (@to_wedge_bij i))).
  by rewrite path_zero.
by apply/mem_set.
Qed.

Local Lemma from_wedge_one : from_wedge_sub one = one.
Proof.
move/bij_inj : (@to_wedge_bij i); apply.
rewrite /from_wedge_sub /=. 
have /= -> := (@invK _ _ _ _ (bijection_of_bijective (@to_wedge_bij i))).
  by rewrite path_one.
exact/mem_set.
Qed.

Local Lemma from_wedge_cts : continuous from_wedge_sub.
Proof.
apply/continuousP => A /to_wedge_open.
congr(_ _); rewrite eqEsubset; split => //.
  move=> ? /= [z Az <-]; rewrite /from_wedge_sub.
  by rewrite funK => //; apply/mem_set.
move=> z /=; exists (from_wedge_sub z) => //.
rewrite /from_wedge_sub.
have /= -> // := (@invK _ _ _ _ (bijection_of_bijective (@to_wedge_bij i))).
exact/mem_set.
Qed.

HB.instance Definition _ := isContinuous.Build _ _ from_wedge_sub from_wedge_cts.

HB.instance Definition _ := isPath.Build (bpwedge i i) i zero one from_wedge_sub
  from_wedge_zero from_wedge_one.
End self_wedge_path.

HB.lock Definition from_wedge {i : selfSplitType} : 
    {path (bpwedge i i) from zero to one in i} := 
  [the pathType _ _ _ of from_wedge_sub].

Lemma from_wedgeK {i : selfSplitType} : cancel from_wedge (@to_wedge i).
Proof.
move=> z; rewrite unlock /= /from_wedge_sub.
have /= -> // := (@invK _ _ _ _ (bijection_of_bijective (@to_wedge_bij i))).
exact/mem_set.
Qed.

Lemma to_wedgeK {i : selfSplitType}: cancel (@to_wedge i) from_wedge.
Proof.
by move=> z; rewrite unlock /= /from_wedge_sub funK //; exact/mem_set.
Qed.

Section path_join_assoc. 
Context (i : selfSplitType).

Let i_i := @bpwedge i i.
Local Open Scope quotient_scope.
Notation "f '<>' g" := (@path_concat _ i _ _ _ f g).

Lemma conact_cstr {T : topologicalType} (x y : T) (f : {path i from x to y}) :
  exists (p : {path i from zero to one}), f \o p = (f <> cst y).
Proof.
exists (idfun <> cst one). 
rewrite compA wedge_fun_comp /path_concat.
congr( _ \o to_wedge); congr(wedge_fun _).
apply: functional_extensionality_dep; case => //=.
by apply/funext => ? /=; rewrite /cst path_one.
Qed.

Lemma conact_cstl {T : topologicalType} (x y : T) (f : {path i from x to y}) :
  exists (p : {path i from zero to one}), f \o p = (cst x <> f).
Proof.
exists (cst zero <> idfun). 
rewrite compA wedge_fun_comp /path_concat.
congr( _ \o to_wedge); congr(wedge_fun _).
apply: functional_extensionality_dep; case => //=.
by apply/funext => ? /=; rewrite /cst path_zero.
Qed.

Let ii_i := (bpwedge i_i i).
Let i_ii := (bpwedge i i_i).
Check @mk_path.
Let wedgel_i_i : {path i from zero to _ in i_i} := 
  @mk_path _ _ zero _
    [the continuousType _ _ of @wedge_lift _ _ _ true] 
    cts_fun
    erefl (bpwedgeE i i).
  Check wedgel_i_i.
Let wedger_i_i : {path i from _ to one in i_i} :=
  @mk_path _ _ _ one
    [the continuousType _ _ of @wedge_lift _ _ _ false] 
    cts_fun
    erefl erefl.

Let splitl_left : {path i_i from zero to _ in ii_i} := 
  (@mk_path _ _ zero _ 
      [the continuousType _ _ of @wedge_lift _ _ _ true] 
    cts_fun
    erefl (@bpwedgeE _ _)).
Let splitl_right : {path i from _ to one in ii_i} := 
  @mk_path _ _ _ one 
    [the continuousType _ _ of @wedge_lift _ _ _ false] 
    cts_fun
    erefl erefl.
Let splitl : {path i from (@zero ii_i) to one} := 
  (reparameterize splitl_left to_wedge) <> splitl_right.

Let splitr_right : {path i_i from _ to one in i_ii} := 
  @mk_path _ _ _ one
    [the continuousType _ _ of @wedge_lift _ _ _ false]
    cts_fun
    erefl erefl.
Let splitr_left : {path i from zero to _ in i_ii} := 
  @mk_path _ _ zero _ 
    [the continuousType _ _ of @wedge_lift _ _ _ true]
    cts_fun
     erefl (bpwedgeE _ _).

Let unsplitr : {path i_ii from zero to one in i} := 
  reparameterize 
    from_wedge 
    (chain_path wedgel_i_i (reparameterize wedger_i_i from_wedge)).
  
Let associ : continuousType ii_i i_ii := 
  chain_path 
    (chain_path 
      (splitr_left)
      (splitr_right \o wedgel_i_i))
    (splitr_right \o wedger_i_i).

Section assoc.
Context {T : topologicalType} {p1 p2 p3 p4: T}. 
Context (f : {path i from p1 to p2}).
Context (g : {path i from p2 to p3}).
Context (h : {path i from p3 to p4}).

Local Lemma assoc0 : associ zero = zero.
Proof.
rewrite /associ /= /chain_path/mk_path /= ?wedge_lift_funE //.
  by case; case; rewrite //= ?bpwedgeE.
case; case; rewrite //= ?bpwedgeE //= ?wedge_lift_funE /= ?bpwedgeE //=.
  by case; case; rewrite //= ?bpwedgeE.
by case; case; rewrite //= ?bpwedgeE.
Qed.

Local Lemma assoc1 : associ one = one.
Proof.
rewrite /associ /= /chain_path/mk_path /= ?wedge_lift_funE //.
case; case; rewrite //= ?bpwedgeE //= ?wedge_lift_funE /= ?bpwedgeE //=.
  by case; case; rewrite //= ?bpwedgeE.
by case; case; rewrite //= ?bpwedgeE.
Qed.
 
(* not really non-forgetful, but we can make it local anyway so it's fine*)
#[local, non_forgetful_inheritance]
HB.instance Definition _ := isPath.Build ii_i _ _ _ associ
  assoc0 assoc1.

Local Lemma concat_assocl : 
  (f <> (g <> h)) \o (unsplitr \o associ \o splitl) = 
    ((f <> g) <> h).
Proof.
Ltac wedge_simpl := repeat (
    rewrite ?(wedge_lift_funE, path_one, path_zero, bpwedgeE, reprK) //=;
  (try (case;case))).
apply/funext => z; rewrite /= /reparameterize /=/associ/chain_path.
rewrite -[to_wedge z](@reprK _ i_i). 
case E : (repr (to_wedge z)) => [b x] /=.
wedge_simpl;  rewrite /= ?from_wedgeK ?to_wedgeK.
case: b x E => x E /=; wedge_simpl; first last.
  by rewrite from_wedgeK; wedge_simpl.
rewrite -[to_wedge x](@reprK _ i_i); case: (repr (to_wedge x)) => [b2 y] /=.
case: b2 y => y; wedge_simpl; rewrite from_wedgeK.
wedge_simpl.
Qed.
  
Lemma concat_assoc: 
  exists p : {path i from zero to one}, 
    (f <> (g <> h)) \o p = ((f <> g) <> h).
Proof.
exists (reparameterize unsplitr (reparameterize associ splitl)). 
by rewrite concat_assocl. 
Qed.

End assoc.
End path_join_assoc.

HB.mixin Record isPathDomain {d} (i : Type) of 
  OrderTopological d i & SelfSplit i := {
  (* this makes the path_between relation symmetric*)
  flip : {path i from (@one i) to (@zero i)};
  flipK : involutive flip;
  (* this lets us curry for paths between paths*)
  domain_locally_compact : locally_compact [set: i];
  (* this gives us starting/ending points for constructing homotopies*)
  zero_bot : forall (y : i), (@Order.le d i zero y);
  one_top : forall (y : i), (@Order.le d i y one);
}.

#[short(type="pathDomainType")]
HB.structure Definition PathDomain {d} := 
  { i of @OrderTopological d i & SelfSplit i & isPathDomain d i}.

Lemma path_domain_set1 {d} {i : pathDomainType d} (x : i) : 
  closed [set x].
Proof.
exact/accessible_closed_set1/hausdorff_accessible/order_hausdorff.
Qed.

#[global] Hint Resolve path_domain_set1 : core.

Section path_flip.
Context {d} {T : topologicalType} (i : pathDomainType d) (x y : T).
Context (f : {path i from x to y}).

Definition path_flip := f \o flip.

Local Lemma fflip_zero : path_flip zero = y.
Proof. by rewrite /path_flip /= path_zero path_one. Qed.

Local Lemma fflip_one : path_flip one = x.
Proof. by rewrite /path_flip /= path_one path_zero. Qed.

Local Lemma fflip_cts : continuous path_flip.
Proof. by move=> ?; apply: continuous_comp; apply: cts_fun. Qed.

HB.instance Definition _ := isContinuous.Build _ _ path_flip fflip_cts.

HB.instance Definition _ := isPath.Build i T y x path_flip
  fflip_zero fflip_one.
End path_flip.
