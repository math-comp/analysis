(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssrnat eqtype choice fintype order bigop ssralg.
From mathcomp Require Import ssrnum.
Require Import boolp reals ereal.
Require Import classical_sets posnum topology normedtype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Reserved Notation "{ 'ae' P }" (at level 0, format "{ 'ae'  P }").

(* TODO d'ordre general:
   1. better lim notation *)

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Definition fct_sequence (R : numDomainType) (T : Type) := nat -> (T -> {ereal R}).

Definition increasing (R : numDomainType) (T : Type) (D : set T) (f_ : fct_sequence R T) :=
  forall n, (forall x, D x -> real_of_er (f_ n x) <= real_of_er (f_ n.+1 x)).

Module Type INTEGRAL.

Module Measurable.

Parameter class_of : forall (T : Type), Type.
Notation sigma_algebra := class_of.

Parameter sets : forall T, class_of T -> set (set T).

Structure type := Pack {
  sort : Type ; class : class_of sort }.

Module Exports.
Notation measurableType := type.
Coercion sort : type >-> Sortclass.
Definition measurable (T : type) := sets (class T).
Notation sigma_algebra := class_of.
End Exports.

(* TODO: property that all measurable sets are indeed measurable *)

End Measurable.

Export Measurable.Exports.

Parameter measurable_fun : forall (R : numDomainType) (T : measurableType) (f : T -> {ereal R}), bool.

Parameter integral :
  forall (R : numDomainType) (T : measurableType) (m : set T -> {ereal R}) (D : set T) (f : T -> {ereal R}), {ereal R}.

(* NB: integrable to be defined as measurable and of finite integral
of absolute value *)
Parameter integrable :
  forall (R : numDomainType) (T : measurableType) (m : set T -> {ereal R}) (D : set T) (f : T -> {ereal R}), bool.

Definition almost_everywhere (R : numDomainType) (T : measurableType) (m : set T -> {ereal R})
  (P : T -> Prop) & (phantom Prop (forall x, P x)) :=
  exists A : set T, measurable A /\ m A = 0%:E /\ forall x, A x \/ P x.
(* TODO: issue remove the Coercion real : Rbar >-> R in Rbar.v*)
Notation "{ 'ae' m , P }" := (almost_everywhere m (inPhantom P))
  (at level 0, format "{ 'ae'  m ,  P }") : type_scope.

(* section about positive or infinite functions *)
Section pos_fct.
Variable R : numFieldType.
Variable T : measurableType.
Variable m : set T -> {ereal R}.
Variable D : set T.

(* TODO: we have to restrict linearity to:
   1. positive and measurable
   2. integrable functions
   (Need two "integral" symbols for Canonical declarations?) *)
Axiom integral_is_linear :
  linear_for *%R ((fun f => real_of_er (integral m D (fun x => (f x)%:E))) : (T -> R^o) -> R).
Canonical integral_linear := Linear integral_is_linear.

(* TODO: order structure about functions
Axiom fct_order : forall (T : Type) (f g : T -> R), bool.
in order to be able to use the notation {homo ...}
in order to rewrite the lemma integral_ler *)

Axiom integral_ler : forall (f g : T -> R),
  (forall x, f x <= g x) -> real_of_er (integral m D (fun x => (f x)%:E)) <= real_of_er (integral m D (fun x => (g x)%:E)).
(* TODO: need two variants
   1. take into account that diverge(f) -> diverge(g)
   2. when we talk only about measurable functions
*)

(* monotone convergence theorem:
   voir necessite de la condition de positivite (wikipedia.fr),
   pas de variante pour les fonctions non-necessairement positive
   (no variant 2., see convergence dominee) *)
Axiom cvg_monotone :
  forall (f_ : fct_sequence R T) (*should be positive*),
  (forall n, measurable_fun (f_ n)) ->
  increasing D f_ ->
  let f := fun t => lim ((fun n => real_of_er (f_ n t)) : nat -> R^o) in
  measurable_fun (fun x => (f x)%:E) /\
  real_of_er (integral m D (fun x => (f x)%:E)) = lim ((fun n => real_of_er (integral m D (f_ n))) : nat -> R^o).

(* TODO: Fatou's Lemma *)

End pos_fct.

(* section about other functions (returning finite values),
   requires preconditions about integrability, etc. *)
Section fin_fct.
Variable R : numFieldType.
Variable T : measurableType.
Variable m : set T -> R.
Variable D : set T.

(* dominated convergence theorem *)
Axiom cvg_dominated : forall (f_ : fct_sequence R T) (f : T -> R) (g : T -> R),
  (forall n, integrable (fun x => (m x)%:E) D (f_ n)) ->
  integrable (fun x => (m x)%:E) D (fun x => (g x)%:E) ->
  (forall n, {ae (fun x => (m x)%:E), forall x, `| real_of_er (f_ n x) | <= g x}) ->
  {ae (fun x => (m x)%:E), forall x, ((fun n => (real_of_er (f_ n x) : R)) : nat -> R^o) --> (f x : R^o)} ->
  (fun n => real_of_er (integral (fun x => (m x)%:E) D (f_ n))) @ \oo --> (real_of_er (integral (fun x => (m x)%:E) D (fun x => (f x)%:E)) : R^o).

End fin_fct.

(* TODO *)
Axiom product_measure : forall (R : numFieldType) (X Y : measurableType)
  (mx : set X -> R) (my : set Y -> R), set (X * Y) -> R.
Axiom product_measurableType_sigma_algebra : forall (X Y : measurableType), sigma_algebra (X * Y).
Canonical product_measurableType X Y := Measurable.Pack (product_measurableType_sigma_algebra X Y).
Axiom sigma_algebra_completion : forall (R : numFieldType) (T : Type) (X : sigma_algebra T) (mx : set T -> R),
 sigma_algebra T.
Definition measurable_completion (R : numFieldType) (X : measurableType) (m : set X -> {ereal R}) :=
  @Measurable.Pack X (sigma_algebra_completion (Measurable.class X) (fun x => real_of_er (m x))).

Section fubini.

Variables (R : numFieldType) (X Y : measurableType).
Variables (mx : set X -> R) (my : set Y -> R).
Let mz : set (X * Y) -> R := product_measure mx my.
Variable f : @measurable_completion R (product_measurableType X Y) (fun x => (mz x)%:E) -> {ereal R}.

(* see faraut p.61 *)
Axiom fubini_tonelli : measurable_fun f ->
  (forall x, 0 <= real_of_er (f x)) ->
  let F := fun x => integral (fun x => (my x)%:E) setT (fun y => f (x, y)) in
  measurable_fun F /\
  integral (fun x => (mz x)%:E) setT f = integral (fun x => (mx x)%:E) setT F.

End fubini.

(* wip *)

(* TODO: see also definitions in sequences.v *)
Definition nondecreasing (T : measurableType) (u_ : nat -> set T) :=
  forall n, u_ n `<=` u_ n.+1.

Lemma nondecreasing_ler (T : measurableType) (u_ : nat -> set T) :
  nondecreasing u_ -> {homo u_ : n m / (n <= m)%nat >-> n `<=` m}.
Proof.
move=> iu n; elim=> [|m ih]; first by rewrite leqn0 => /eqP ->.
rewrite leq_eqVlt => /orP[/eqP <- //|].
by rewrite ltnS => /ih/subset_trans; apply; apply iu.
Qed.

Definition triviset X (A : nat -> set X) :=
  forall j i, (i != j)%nat -> A i `&` A j = set0.

Axiom ereallim : forall (R : numFieldType), (nat -> {ereal R}) -> {ereal R}.

Section additivity.
Variables (R : numFieldType) (X : Type) (mx : set X -> {ereal R}).
Definition additive := forall A, triviset A -> forall n,
  mx (\bigcup_(i in (fun k => (k <= n)%N)) A i) = (\sum_(i < n.+1) mx (A i))%E.
Definition sigma_additive := forall A, triviset A ->
  mx (\bigcup_n A n) = ereallim (fun n => (\sum_(i < n.+1) mx (A i))%E).
End additivity.

Lemma additive2 (R : numFieldType) X (mx : set X -> {ereal R}) :
  additive mx -> forall A B, A `&` B = set0 -> mx (A `|` B) = (mx A + mx B)%E.
Proof.
move=> amx A B AB.
set C := fun n => if n isn't n'.+1 then A else if n' is O then B else set0.
rewrite (_ : _ `|` _ = \bigcup_(i in (fun k => (k <= 1)%N)) C i); last first.
  rewrite funeqE => x; rewrite propeqE; split.
  move=> -[Ax|Bx]; by [exists O | exists 1%nat].
  move=> -[[/= _ ?|[|]]]; [by left | by right|by case].
rewrite amx; last first.
  move=> [[//|[_|_ _] /=]|].
  by rewrite setIC.
  by rewrite set0I.
  move=> [|] /=; last by move=> *; rewrite setI0.
  by move=> [//|[//|/= *]]; rewrite set0I.
by rewrite 2!big_ord_recl /= big_ord0 adde0.
Qed.

Lemma additive_implies_sigma_additive (R : numFieldType) X (mx : set X -> {ereal R}) :
  mx set0 = 0%:E -> sigma_additive mx -> additive mx.
Proof.
move=> mx0 samx B Bset n; set B' := fun i => if (i <= n)%nat then B i else set0.
transitivity (mx (\bigcup_i B' i)).
  congr mx; rewrite funeqE => x; rewrite propeqE; split.
  by move=> -[j jn] ?; exists j => //; rewrite /B' jn.
  by move=> -[j _]; rewrite /B'; case: ifPn => // jn Bj; exists j.
rewrite samx; last first.
  move=> j i ij; rewrite /B' funeqE => x; rewrite propeqE; split => //.
  move=> -[]; case : ifPn => // ni Bi; case: ifPn => // jn Bj.
  by rewrite -(Bset j i).
(*apply/(@cvg_map_lim _ [normedModType R of R^o]).
move=> /= s [e e0 es]; exists n.+1 => // m nm; apply es => /=.
rewrite (_ : _ - _ = 0) ?normr0 //; apply/eqP; rewrite subr_eq0; apply/eqP.
rewrite -(@big_mkord _ _ _ m.+1 xpredT (fun i => mx (B' i))).
rewrite -(@subnKC n.+1 m.+1) 1?ltnW // /index_iota subn0 iota_add big_cat.
rewrite -[in X in _ = X + _](subn0 n.+1) -/(index_iota 0 n.+1).
rewrite big_mkord /= add0n [X in _ = _ + X]big1_seq ?addr0; last first.
  move=> /= i; rewrite mem_iota subnKC; last exact/ltnW.
  by move=> /andP[ni im]; rewrite /B' leqNgt ni /= mx0.
by apply eq_bigr => i _; rewrite /B' -ltnS ltn_ord.
Qed.*)
Admitted.

Section properties_of_measures.
Variables (R : numFieldType) (X : measurableType) (mx : set X -> {ereal R}).
Axiom measurable0 : mx set0 = 0%:E.
Axiom measurable_ge0 : forall x, (0%:E <= mx x)%E.
Axiom measurable_sigma_additive : sigma_additive mx.
End properties_of_measures.

Lemma lee_addl (R : numDomainType) (x y : {ereal R}) : (0%:E <= y)%E ->  (x <= x + y)%E.
Proof.
by move: x y => -[ x [y| |]//= | [| |]// | [| | ]//]; rewrite !lee_fin ler_addl.
Qed.

Lemma lee_add2l (R : numDomainType) (x a b : {ereal R}) :
  (a <= b)%E -> (x + a <= x + b)%E.
Proof.
move: a b x => -[a [b [x /=|//|//] | []// |//] | []// | ].
  by rewrite !lee_fin ler_add2l.
by move=> -[b [|  |]// | [] | //].
Qed.

Lemma lee_add2r (R : numDomainType) (x a b : {ereal R}) :
  (a <= b)%E -> (a + x <= b + x)%E.
Proof. rewrite addeC (addeC b); exact: lee_add2l. Qed.

(* measure is monotone *)
Lemma measure_monotone (R : numFieldType) (X : measurableType) (mx : set X -> {ereal R}) :
  {homo mx : A B / A `<=` B >-> (A <= B)%E}.
Proof.
move=> A B AB; have {1}-> : B = A `|` (B `\` A).
  rewrite funeqE => x; rewrite propeqE.
  have [Ax|Ax] := pselect (A x).
  split=> [Bx|]; by [left | move=> -[/AB //|] []].
  split=> [Bx|]; by [right| move=> -[//|] []].
rewrite additive2 // ?lee_addl //.
exact: measurable_ge0.
apply additive_implies_sigma_additive.
exact: measurable0.
exact: measurable_sigma_additive.
rewrite setDE setICA (_ : _ `&` ~` _ = set0) ?setI0 //.
by rewrite funeqE => x; rewrite propeqE; split => // -[].
Qed.

Section boole_inequality.
Variables (R : numFieldType) (X : measurableType) (mx : set X -> {ereal R}).

(* measure is continuous from below *)
Lemma measure_bigcup (A : nat -> set X) : nondecreasing A ->
  mx (\bigcup_n A n) = ereallim (mx \o A).
Proof.
move=> ndA.
set B := fun n => if n isn't n'.+1 then A O else A n `\` A n'.
have Binter : triviset B.
  move=> j i; wlog : j i / (i < j)%nat.
    move=> h; rewrite neq_ltn => /orP[|] ?; by
      [rewrite h // ltn_eqF|rewrite setIC h // ltn_eqF].
  move=> ij _; move: j i ij; case => // j [_ /=|n].
    rewrite funeqE => x; rewrite propeqE; split => // -[A0 [Aj1 Aj]].
    by apply Aj; apply: nondecreasing_ler A0.
  rewrite ltnS => nj /=; rewrite funeqE => x; rewrite propeqE; split => //.
  by move=> -[[An1 An] [Aj1 Aj]]; apply Aj; apply: nondecreasing_ler An1.
have ABE : forall n, A n.+1 = A n `|` B n.+1.
  move=> n; rewrite /B funeqE => x; rewrite propeqE; split.
  by move=> ?; have [?|?] := pselect (A n x); [left | right].
  by move=> -[|[]//]; apply: ndA.
have AE n : A n = \bigcup_(i in [set k | (k <= n)%nat]) B i.
  elim: n => [|n ih]; rewrite funeqE => x; rewrite propeqE; split.
  - by move=> ?; exists O.
  - by move=> -[?]; rewrite leqn0 => /eqP ->.
  - rewrite ABE => -[|/=].
    by rewrite ih => -[j /leq_trans jn Bjx]; exists j => //; rewrite jn.
    by move=> -[An1x Anx]; exists n.+1.
  - move=> -[[_|j]]; first by rewrite /=; apply: nondecreasing_ler.
    by rewrite /= => jn [Aj1x Ajx]; apply: (nondecreasing_ler ndA _ Aj1x).
have AB : \bigcup_(n in setT) A n = \bigcup_(n in setT) B n.
  rewrite funeqE => x; rewrite propeqE; split.
  by move=> -[n _]; rewrite AE => -[n' _] ?; exists n'.
  by move=> -[n _ ?]; exists n => //; rewrite AE; exists n.
rewrite AB measurable_sigma_additive; last by move=> i j; exact: Binter.
rewrite (_ : (fun n => \sum_(i < n.+1) mx (B i))%E = mx \o A) //.
rewrite funeqE => n; rewrite -additive_implies_sigma_additive // -?AE //.
exact: measurable0.
exact: measurable_sigma_additive.
Qed.

(* measure satisfies Boole's inequality *)
Lemma bool_le (A : nat -> set X) : forall n,
  (mx (\bigcup_(i in (fun k => (k <= n)%N)) A i) <= \sum_(i < n.+1) mx (A i))%E.
Proof.
elim => [|n ih].
  rewrite big_ord_recl big_ord0 adde0 (_ : bigsetU _ _ = A O) //.
  rewrite funeqE => x; rewrite propeqE; split => [|A0x]; last by exists O.
  by move=> -[i]; rewrite leqn0 => /eqP ->.
set B := \bigcup_(i in (fun k => (k <= n)%nat)) A i.
set C := \bigcup_(i in _) A i.
have -> : C = B `|` (A n.+1 `&` ~` B).
  rewrite funeqE => x; rewrite propeqE; split.
    move=> -[j]; rewrite leq_eqVlt => /orP[/eqP ->{j} An1|].
      have [?|?] := pselect (B x); [by left|by right].
    by move=> jn Aj; left; exists j.
  move=> -[[j jn Aj]|]; first by exists j => //; rewrite ltnW.
  by move=> [An1 _]; exists n.+1.
rewrite additive2; last 2 first.
  apply additive_implies_sigma_additive.
  exact: measurable0.
  exact: measurable_sigma_additive.
  rewrite setIC -setIA (_ : ~` _ `&` _ = set0) ?setI0 //.
  by rewrite funeqE => x; rewrite propeqE; split => // -[].
rewrite (@le_trans _ _ (mx B + mx (A n.+1))%E) // ?lee_add2l //.
rewrite measure_monotone //; first by apply subIset; left.
by rewrite big_ord_recr /= lee_add2r.
Qed.

(* measure satisfies generalized Boole's inequality *)
Lemma bool_le_gen (A : nat -> set X) :
  (mx (\bigcup_(n in setT) A n) <= ereallim (fun n => \sum_(i < n) mx (A i)))%E.
Proof.
set B := fun n : nat => \bigcup_(i in [set k | (k <= n)%nat]) (A i).
rewrite [X in mx X](_ : _ = \bigcup_(n in setT) B n); last first.
  rewrite funeqE => x; rewrite propeqE; split.
  by move=> -[k _ Akx]; exists k => //; exists k.
  by move=> -[k _ [k' ? ?]]; exists k'.
rewrite measure_bigcup; last first.
  by move=> n x [n' /leq_trans n'n ?]; exists n' => //; exact: n'n.
Abort.

End boole_inequality.

End INTEGRAL.
