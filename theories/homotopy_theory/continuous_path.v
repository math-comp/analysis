(* mathcomp analysis (c) 2024 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra finmap generic_quotient.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality fsbigop reals topology.
From mathcomp Require Import function_spaces wedge_sigT.

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
