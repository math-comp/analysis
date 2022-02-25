(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice order.
From mathcomp Require Import ssrnat seq fintype bigop div prime path finmap.
From mathcomp Require Import ssralg ssrnum ssrint rat finset.
Require Import boolp mathcomp_extra classical_sets functions.

(******************************************************************************)
(*                              Cardinality                                   *)
(*                                                                            *)
(* This file provides an account of cardinality properties of classical sets. *)
(* This includes standard results of set theory such as the Pigeon Hole       *)
(* principle, the Cantor-Bernstein Theorem, or lemmas about the cardinal of   *)
(* nat, nat * nat, and rat.                                                   *)
(*                                                                            *)
(* Since universe polymorphism is not yet available in our framework, we      *)
(* develop a relational theory of cardinals: there is no type for cardinals   *)
(* only relations A #<= B and A #= B to compare the cardinals of two sets     *)
(* (on two possibly different types).                                         *)
(*                                                                            *)
(*         A #<= B  ==  the cardinal of A is smaller or equal to the one of B *)
(*         A #>= B  := B #<= A                                                *)
(*          A #= B  ==  the cardinal of A is equal to the cardinal of B       *)
(*         A #!= B  := ~~ (A #= B)                                            *)
(*    finite_set A  ==  the set A is finite                                   *)
(*                  :=  exists n, A #= `I_n                                   *)
(*                 <-> exists X : {fset T}, A = [set` X]                      *)
(*                 <-> ~ ([set: nat] #<= A)                                   *)
(*  infinite_set A  := ~ finite_set A                                         *)
(*     countable A <-> A is countable                                         *)
(*                  :=  A #<= [set: nat]                                      *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "A '#<=' B" (at level 79, format "A  '#<='  B").
Reserved Notation "A '#>=' B" (at level 79, format "A  '#>='  B").
Reserved Notation "A '#=' B" (at level 79, format "A  '#='  B").
Reserved Notation "A '#!=' B" (at level 79, format "A  '#!='  B").

Import Order.Theory GRing.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope function_scope.

Declare Scope card_scope.
Delimit Scope card_scope with card.
Local Open Scope card_scope.

Definition card_le T U (A : set T) (B : set U) :=
  `[< $|{injfun [set: A] >-> [set: B]}| >].
Notation "A '#<=' B" := (card_le A B) : card_scope.
Notation "A '#>=' B" := (card_le B A) (only parsing) : card_scope.

Definition card_eq T U (A : set T) (B : set U) := `[<$|{bij [set: A] >-> [set: B]}|>].
Notation "A '#=' B" := (card_eq A B) : card_scope.
Notation "A '#!=' B" := (~~ (card_eq A B)) : card_scope.

Definition finite_set {T} (A : set T) := exists n, A #= `I_n.
Notation infinite_set A := (~ finite_set A).

Lemma injPex {T U} {A : set T} :
   $|{inj A >-> U}| <-> exists f : T -> U, set_inj A f.
Proof. by split=> [[f]|[_ /Pinj[f _]]]; first by exists f. Qed.

Lemma surjPex {T U} {A : set T} {B : set U} :
  $|{surj A >-> B}| <-> exists f, set_surj A B f.
Proof. by split=> [[f]|[_ /Psurj[f _]]]; first by exists f. Qed.

Lemma bijPex {T U} {A : set T} {B : set U} :
  $|{bij A >-> B}| <-> exists f, set_bij A B f.
Proof. by split=> [[f]|[_ /Pbij[f _]]]; first by exists f. Qed.

Lemma surjfunPex {T U} {A : set T} {B : set U} :
  $|{surjfun A >-> B}| <-> exists f, B = f @` A.
Proof.
split=> [[f]|[f ->]]; last by squash [fun f in A].
by exists f; apply/seteqP; split=> //; apply: surj.
Qed.

Lemma injfunPex {T U} {A : set T} {B : set U}:
   $|{injfun A >-> B}| <-> exists2 f : T -> U, set_fun A B f & set_inj A f.
Proof. by split=> [[f]|[_ /Pfun[? ->] /funPinj[f]]]; [exists f | squash f]. Qed.

Lemma card_leP {T U} {A : set T} {B : set U} :
  reflect $|{injfun [set: A] >-> [set: B]}| (A #<= B).
Proof. exact: asboolP. Qed.

Lemma inj_card_le {T U} {A : set T} {B : set U} : {injfun A >-> B} -> (A #<= B).
Proof. by move=> f; apply/card_leP; squash (sigLR f). Qed.

Lemma pcard_leP {T} {U : pointedType} {A : set T} {B : set U} :
   reflect $|{injfun A >-> B}| (A #<= B).
Proof.
by apply: (iffP card_leP) => -[f];
  [squash (valLR point f) | squash (sigLR f)].
Qed.

Lemma pcard_leTP {T} {U : pointedType} {A : set T} :
  reflect $|{inj A >-> U}| (A #<= [set: U]).
Proof.
by apply: (iffP pcard_leP) => -[f]; [squash f | squash ('totalfun_A f)].
Qed.

Lemma pcard_injP {T} {U : pointedType} {A : set T} :
  reflect (exists f : T -> U, {in A &, injective f}) (A #<= [set: U]).
Proof. by apply: (iffP pcard_leTP); rewrite injPex. Qed.

Lemma ppcard_leP {T U : pointedType} {A : set T} {B : set U} :
   reflect $|{splitinjfun A >-> B}| (A #<= B).
Proof. by apply: (iffP pcard_leP) => -[f]; squash (split f). Qed.

Lemma card_ge0 T U (S : set U) : @set0 T #<= S.
Proof. by apply/card_leP; squash set0fun. Qed.
Hint Resolve card_ge0 : core.

Lemma card_le0P T U (A : set T) : reflect (A = set0) (A #<= @set0 U).
Proof.
apply: (iffP idP) => [/card_leP[f]|->//].
by rewrite -subset0 => a /mem_set aA; have [x /set_mem] := f (SigSub aA).
Qed.

Lemma card_le0  T U (A : set T) : (A #<= @set0 U) = (A == set0).
Proof. exact/card_le0P/eqP. Qed.

Lemma card_eqP {T U} {A : set T} {B : set U} :
  reflect $|{bij [set: A] >-> [set: B]}| (A #= B).
Proof. exact: asboolP. Qed.

Lemma pcard_eq {T U} {A : set T} {B : set U} : {bij A >-> B} -> A #= B.
Proof. by move=> f; apply/card_eqP; squash (sigLR f). Qed.

Lemma pcard_eqP {T} {U : pointedType} {A : set T} {B : set U} :
   reflect $| {bij A >-> B} | (A #= B).
Proof.
by apply: (iffP card_eqP) => -[f]; [squash (valLR point f) | squash (sigLR f)].
Qed.

Lemma card_bijP {T U} {A : set T} {B : set U} :
   reflect (exists f : A -> B, bijective f) (A #= B).
Proof.
by apply: (iffP card_eqP) => [[f]|[_ /PbijTT[f _]]]; [exists f|squash f].
Qed.

Lemma card_eqVP {T U} {A : set T} {B : set U} :
   reflect $|{splitbij [set: A] >-> [set: B]}| (A #= B).
Proof. by apply: (iffP card_bijP) => [[_ /PbijTT[f _]]//|[f]]; exists f. Qed.

Lemma card_set_bijP {T} {U : pointedType} {A : set T} {B : set U} :
   reflect (exists f, set_bij A B f) (A #= B).
Proof.
by apply: (iffP pcard_eqP) => [[f]|[_ /Pbij[f _]]]; [exists f|squash f].
Qed.

Lemma ppcard_eqP {T U : pointedType} {A : set T} {B : set U} :
   reflect $| {splitbij A >-> B} | (A #= B).
Proof. by apply: (iffP pcard_eqP) => -[f]; [squash (split f)|squash f]. Qed.

Lemma card_eqxx T (A : set T) : A #= A.
Proof. by apply/card_eqP; squash idfun. Qed.
Hint Resolve card_eqxx : core.

Lemma card_eq00 T U : @set0 T #= @set0 U.
Proof.
apply/card_eqP/squash; apply: @bijection_of_bijective set0fun _.
by exists set0fun => -[x x0]; have := set_mem x0.
Qed.
Hint Resolve card_eq00 : core.

Section empty1.
Implicit Types (T : emptyType).
Lemma empty_eq0 T : all_equal_to (set0 : set T).
Proof. by move=> X; apply/setF_eq0/no. Qed.
Lemma card_le_emptyl T U (A : set T) (B : set U) : A #<= B.
Proof. by rewrite empty_eq0. Qed.
Lemma card_le_emptyr T U (A : set T) (B : set U) : (B #<= A) = (B == set0).
Proof. by rewrite empty_eq0; apply/idP/eqP=> [/card_le0P|->//]. Qed.

Definition emptyE_subdef := (empty_eq0, card_le_emptyl, card_le_emptyr, eq_opE).
End empty1.

Theorem Cantor_Bernstein T U (A : set T) (B : set U) :
  A #<= B -> B #<= A -> A #= B.
Proof.
elim/Ppointed: T => T in A *; first by rewrite !emptyE_subdef => _ ->.
elim/Ppointed: U => U in B *; first by rewrite !emptyE_subdef => ->.
suff {A B} card_eq (A B : set U) : B `<=` A -> A #<= B -> A #= B.
  move=> /ppcard_leP[f] /ppcard_leP[g].
  have /(_ _)/ppcard_eqP[|h] := card_eq _ _ (fun_image_sub f).
    by apply/pcard_leP; squash ([fun f in A] \o g).
  by apply/pcard_eqP; squash ((split h)^-1 \o [fun f in A]).
move=> BA /ppcard_leP[u]; have uAB := 'funS_u.
pose C_ := fix C n := if n is n.+1 then u @` C n else A `\` B.
pose C := \bigcup_n C_ n; have CA : C `<=` A.
  by move=> + [] => /[swap]; elim=> [|i IH] y _ []// x /IH/uAB/BA + <-; apply.
have uC: {homo u : x / x \in C}.
  by move=> x; rewrite !inE => -[i _ Cix]; exists i.+1 => //; exists x.
apply/card_set_bijP; exists (fun x => if x \in C then u x else x); split.
- move=> x Ax; case: ifPn; first by move=> _; apply: uAB.
  by move/negP; apply: contra_notP => NBx; rewrite inE; exists 0%N.
- move=> x y xA yA; have := 'inj_u xA yA.
  have [xC|] := boolP (x \in C); have [yC|] := boolP (y \in C) => // + _.
    by move=> /[swap]<-; rewrite uC// xC.
  by move=> /[swap]->; rewrite uC// yC.
- move=> y /[dup] By /BA Ay/=.
  case: (boolP (y \in C)); last by exists y; rewrite // ifN.
  rewrite inE => -[[|i]/= _ []// x Cix <-]; have Cx : C x by exists i.
  by exists x; [exact: CA|rewrite ifT// inE].
Qed.

Lemma card_esym T U (A : set T) (B : set U) : A #= B -> B #= A.
Proof. by move=> /card_eqVP[f]; apply/card_eqP; squash f^-1. Qed.

Lemma card_eq_le T U (A : set T) (B : set U) :
  (A #= B) = (A #<= B) && (B #<= A).
Proof.
apply/idP/andP => [/card_eqVP[f]|[]]; last exact: Cantor_Bernstein.
by split; apply/card_leP; [squash f|squash f^-1].
Qed.

Lemma card_eqPle T U (A : set T) (B : set U) :
  (A #= B) <-> (A #<= B) /\ (B #<= A).
Proof. by rewrite card_eq_le (rwP andP). Qed.

Lemma card_lexx T (A : set T) : A #<= A.
Proof. by apply/card_leP; squash idfun. Qed.
Hint Resolve card_lexx : core.

Lemma card_leT T (S : set T) : (S #<= [set: T]).
Proof. by apply/card_leP; squash (to_setT \o inclT _ \o val). Qed.

Lemma subset_card_le T (A B : set T) : A `<=` B -> A #<= B.
Proof. by move=> AB; apply/card_leP; squash (inclT _ \o subfun AB). Qed.

Lemma card_image_le {T U} (f : T -> U) (A : set T) : f @` A #<= A.
Proof.
elim/Ppointed: T => T in A f *; first by rewrite !emptyE_subdef image_set0.
by apply/pcard_leP; squash (pinv A f).
Qed.

Lemma inj_card_eq {T U} {A} {f : T -> U} : {in A &, injective f} -> f @` A #= A.
Proof. by move=> /inj_bij/pcard_eq/card_esym. Qed.
Arguments inj_card_eq {T U A f}.

Lemma card_some {T} {A : set T} : some @` A #= A.
Proof. exact: inj_card_eq. Qed.

Lemma card_image {T U} {A : set T} (f : {inj A >-> U}) : f @` A #= A.
Proof. exact: inj_card_eq. Qed.

Lemma card_imsub {T U} (A : set T) (f : {inj A >-> U}) X : X `<=` A -> f @` X #= X.
Proof. by move=> XA; rewrite (card_image [inj of f \o incl XA]). Qed.

Lemma card_le_trans (T U V : Type) (B : set U) (A : set T) (C : set V) :
  A #<= B -> B #<= C -> A #<= C.
Proof. by move=> /card_leP[f]/card_leP[g]; apply/card_leP; squash (g \o f). Qed.

Lemma card_eq_sym T U (A : set T) (B : set U) : (A #= B) = (B #= A).
Proof. by rewrite !card_eq_le andbC. Qed.

Lemma card_eq_trans T U V (A : set T) (B : set U) (C : set V) :
  A #= B -> B #= C -> A #= C.
Proof. by move=> /card_eqP[f]/card_eqP[g]; apply/card_eqP; squash (g \o f). Qed.

Lemma card_le_eql T T' T'' (A : set T) (B : set T') [C : set T''] :
   A #= B -> (A #<= C) = (B #<= C).
Proof. by move=> /card_eqPle[*]; apply/idP/idP; apply: card_le_trans. Qed.

Lemma card_le_eqr T T' T'' (A : set T) (B : set T') [C : set T''] :
   A #= B -> (C #<= A) = (C #<= B).
Proof. by move=> /card_eqPle[*]; apply/idP/idP => /card_le_trans; apply. Qed.

Lemma card_eql T T' T'' (A : set T) (B : set T') [C : set T''] :
   A #= B -> (A #= C) = (B #= C).
Proof. by move=> e; rewrite !card_eq_le (card_le_eql e) (card_le_eqr e). Qed.

Lemma card_eqr T T' T'' (A : set T) (B : set T') [C : set T''] :
   A #= B -> (C #= A) = (C #= B).
Proof. by move=> e; rewrite !card_eq_le (card_le_eql e) (card_le_eqr e). Qed.

Lemma card_ge_image {T U V} {A : set T} (f : {inj A >-> U}) X (Y : set V) :
  X `<=` A -> (f @` X #<= Y) = (X #<= Y).
Proof. by move=> XA; rewrite (card_le_eql (card_imsub _ _)). Qed.

Lemma card_le_image {T U V} {A : set T} (f : {inj A >-> U}) X (Y : set V) :
  X `<=` A -> (Y #<= f @` X) = (Y #<= X).
Proof. by move=> XA; rewrite (card_le_eqr (card_imsub _ _)). Qed.

Lemma card_le_image2 {T U} (A : set T) (f : {inj A >-> U}) X Y :
   X `<=` A -> Y `<=` A ->
   (f @` X #<= f @` Y) = (X #<= Y).
Proof. by move=> *; rewrite card_ge_image// card_le_image. Qed.

Lemma card_eq_image {T U V} {A : set T} (f : {inj A >-> U}) X (Y : set V) :
  X `<=` A -> (f @` X #= Y) = (X #= Y).
Proof. by move=> XA; rewrite (card_eql (card_imsub _ _)). Qed.

Lemma card_eq_imager {T U V} {A : set T} (f : {inj A >-> U}) X (Y : set V) :
  X `<=` A -> (Y #= f @` X) = (Y #= X).
Proof. by move=> XA; rewrite (card_eqr (card_imsub _ _)). Qed.

Lemma card_eq_image2 {T U} (A : set T) (f : {inj A >-> U}) X Y :
   X `<=` A -> Y `<=` A ->
   (f @` X #= f @` Y) = (X #= Y).
Proof. by move=> *; rewrite card_eq_image// card_eq_imager. Qed.

Lemma card_ge_some {T T'} {A : set T} {B : set T'} :
  (some @` A #<= B) = (A #<= B).
Proof. by rewrite (card_le_eql card_some). Qed.

Lemma card_le_some {T T'} {A : set T} {B : set T'} :
  (A #<= some @` B) = (A #<= B).
Proof. by rewrite (card_le_eqr card_some). Qed.

Lemma card_le_some2 {T T'} {A : set T} {B : set T'} :
  (some @` A #<= some @` B) = (A #<= B).
Proof. by rewrite card_ge_some card_le_some. Qed.

Lemma card_eq_somel {T T'} {A : set T} {B : set T'} :
  (some @` A #= B) = (A #= B).
Proof. by rewrite (card_eql card_some). Qed.

Lemma card_eq_somer {T T'} {A : set T} {B : set T'} :
  (A #= some @` B) = (A #= B).
Proof. by rewrite (card_eqr card_some). Qed.

Lemma card_eq_some2 {T T'} {A : set T} {B : set T'} :
  (some @` A #= some @` B) = (A #= B).
Proof. by rewrite card_eq_somel card_eq_somer. Qed.

Lemma card_eq0 {T U} {A : set T} : (A #= @set0 U) = (A == set0).
Proof. by rewrite card_eq_le card_le0 card_ge0 andbT. Qed.

Lemma card_eq_emptyr (T : emptyType) U (A : set T) (B : set U) :
  (B #= A) = (B == set0).
Proof. by rewrite empty_eq0; exact: card_eq0. Qed.

Lemma card_eq_emptyl (T : emptyType) U (A : set T) (B : set U) :
  (A #= B) = (B == set0).
Proof. by rewrite card_eq_sym card_eq_emptyr. Qed.

Definition emptyE := (emptyE_subdef, card_eq_emptyr, card_eq_emptyl).

Lemma card_setT T (A : set T) : [set: A] #= A.
Proof. by apply/card_esym/card_eqP; squash to_setT. Qed.
Hint Resolve card_setT : core.

Lemma card_setT_sym T (A : set T) : A #= [set: A].
Proof. exact/card_esym/card_setT. Qed.
Hint Resolve card_setT : core.

Lemma surj_card_ge {T U} {A : set T} {B : set U} : {surj B >-> A} -> A #<= B.
Proof.
by move=> g; rewrite (card_le_trans (subset_card_le 'surj_g)) ?card_image_le.
Qed.
Arguments surj_card_ge {T U A B} g.

Lemma pcard_surjP {T : pointedType} {U} {A : set T} {B : set U} :
  reflect (exists g, set_surj B A g) (A #<= B).
Proof.
apply: (iffP idP) => [|[_ /Psurj[g _]]]; last exact: surj_card_ge.
elim/Ppointed: U => U in B *; first by rewrite ?emptyE => ->; exists any.
by move=> /pcard_leP[f]; exists (pinv A f); apply: subl_surj surj.
Qed.

Lemma pcard_geP {T : pointedType} {U} {A : set T} {B : set U} :
  reflect $|{surj B >-> A}| (A #<= B).
Proof. by apply: (iffP pcard_surjP); rewrite surjPex. Qed.

Lemma ocard_geP {T U} {A : set T} {B : set U} :
  reflect $|{surj B >-> some @` A}| (A #<= B).
Proof.
by elim/Pchoice: T => T in A *; rewrite -card_ge_some; apply: pcard_geP.
Qed.

Lemma pfcard_geP {T U} {A : set T} {B : set U} :
  reflect (A = set0 \/ $|{surjfun B >-> A}|) (A #<= B).
Proof.
apply: (iffP idP); last by move=> [->//|[f]]; apply: surj_card_ge; exact: f.
elim/Ppointed: T => T in A *; first by rewrite !emptyE; left.
elim/Ppointed: U => U in B *; first by rewrite !emptyE => ->; right; squash any.
move=> /pcard_geP[f]; case: (eqVneq A set0); first by left.
move=> /set0P[x Ax]; right; apply/surjfunPex.
exists (fun y => if f y \in A then f y else x).
apply/seteqP; split.
  by move=> x' /[dup] /= /'surj_f [y By <-] Afy; exists y; rewrite ?ifT// inE.
by apply/image_subP => y By; case: ifPn; rewrite (inE, notin_set).
Qed.

Lemma card_le_II n m : (`I_n #<= `I_m) = (n <= m)%N.
Proof.
apply/idP/idP=> [/card_leP[f]|?];
  last by apply/subset_card_le => k /leq_trans; apply.
by have /leq_card := in2TT 'inj_(IIord \o f \o IIord^-1); rewrite !card_ord.
Qed.

Lemma ocard_eqP {T U} {A : set T} {B : set U} :
  reflect $|{bij A >-> some @` B}| (A #= B).
Proof.
elim/Pchoice: U => U in B *.
by rewrite -(card_eqr card_some); exact: (iffP pcard_eqP).
Qed.

Lemma oocard_eqP {T U} {A : set T} {B : set U} :
  reflect $|{splitbij some @` A >-> some @` B}| (A #= B).
Proof.
elim/Pchoice: U => U in B *; elim/Pchoice: T => T in A *.
rewrite -(card_eql card_some) -(card_eqr card_some).
exact: (iffP ppcard_eqP).
Qed.

Lemma card_eq_II {n m} : reflect (n = m) (`I_n #= `I_m).
Proof. by rewrite card_eq_le !card_le_II -eqn_leq; apply: eqP. Qed.

Lemma sub_setP  {T} {A : set T} (X : set A) : set_val @` X `<=` A.
Proof. by move=> x [/= a Xa <-]; apply: set_valP. Qed.
Arguments sub_setP {T A}.
Arguments image_subset {aT rT} f [A B].

Lemma card_subP T U (A : set T) (B : set U) :
  reflect (exists2 C, C #= A & C `<=` B) (A #<= B).
Proof.
apply: (iffP idP) => [/card_leP[f]|[C CA CB]]; last first.
  by rewrite -(card_le_eql CA); apply/card_leP; squash (inclT _ \o subfun CB).
exists (set_val @` [set of f]); last exact: (subset_trans (sub_setP _)).
by rewrite ?(card_eql (inj_card_eq _))//; apply: in2W; apply: in2TT; apply: inj.
Qed.

(* remove *)
Lemma pigeonhole m n (f : nat -> nat) : {in `I_m &, injective f} ->
  f @` `I_m `<=` `I_n -> (m <= n)%N.
Proof.
move=> /Pinj[{}f->] /subset_card_le.
by rewrite (card_le_eql (inj_card_eq _))// card_le_II.
Qed.

Definition countable T (A : set T) := A #<= @setT nat.

Lemma eq_countable T U (A : set T) (B : set U) :
  A #= B -> countable A = countable B.
Proof. by move=> /card_le_eql leA; rewrite /countable leA. Qed.

Lemma countable_setT_countMixin (T : Type) :
  countable (@setT T) -> Countable.mixin_of T.
Proof.
by move=> /pcard_leP/unsquash f; exists f 'oinv_f; apply: in1TT 'funoK_f.
Qed.

Lemma countableP (T : countType) (A : set T) : countable A.
Proof. by apply/card_leP; squash (to_setT \o choice.pickle). Qed.
Hint Resolve countableP : core.

Lemma countable0 T : countable (@set0 T). Proof. exact: card_ge0. Qed.
Hint Resolve countable0 : core.

Lemma countable_injP T (A : set T) :
  reflect (exists f : T -> nat, {in A &, injective f}) (countable A).
Proof. exact: pcard_injP. Qed.

Lemma sub_countable T U (A : set T) (B : set U) : A #<= B ->
  countable B -> countable A.
Proof. exact: card_le_trans. Qed.

Lemma finite_setP T (A : set T) : finite_set A <-> exists n, A #= `I_n.
Proof. by []. Qed.

Lemma finite_II n : finite_set `I_n. Proof. by apply/finite_setP; exists n. Qed.
Hint Resolve finite_II : core.

Lemma card_II {n} : `I_n #= [set: 'I_n].
Proof. by apply/card_esym/pcard_eqP/bijPex; exists val; split. Qed.

Lemma finite_fsetP {T : choiceType} {A : set T} :
  finite_set A <-> exists X : {fset T}, A = [set` X].
Proof.
rewrite finite_setP; split=> [[n]|[X {A}->]]; last first.
  exists #|{: X}|; rewrite (card_eqr card_II).
  by apply/card_eqP; squash (to_setT \o enum_rank \o val_finset).
rewrite (card_eqr card_II) => /card_esym/card_eqVP[f]; pose g := f \o to_setT.
exists [fset val (g i) | i in 'I_n]%fset.
apply/seteqP; split=> [x /mem_set Ax|_ /imfsetP[i _ ->]]; last exact: set_valP.
by apply/imfsetP; exists (g^-1 (SigSub Ax)); rewrite ?[g _]invK//= inE.
Qed.

Lemma finite_subfset {T : choiceType} (X : {fset T}) {A : set T} :
  A `<=` [set` X] -> finite_set A.
Proof.
move=> AX; apply/finite_fsetP; exists [fset x in X | x \in A]%fset.
apply/seteqP; split=> x; rewrite /= ?inE; last by move=> /andP[_ /set_mem].
by move=> Ax; rewrite mem_set ?andbT//; apply: AX.
Qed.
Arguments finite_subfset {T} X {A}.

Lemma finite_set0 T : finite_set (set0 : set T).
Proof. by apply/finite_setP; exists 0%N; rewrite II0. Qed.
Hint Resolve finite_set0 : core.

Lemma finite_seqP {T : eqType} A :
   finite_set A <-> exists s : seq T, A = [set` s].
Proof.
elim/eqPchoice: T => T in A *; rewrite finite_fsetP.
split=> [[X ->]|[s ->]]; first by exists X.
by exists [fset x | x in s]%fset; apply/seteqP; split=> x /=; rewrite inE.
Qed.

Lemma finite_seq {T : eqType} (s : seq T) : finite_set [set` s].
Proof. by apply/finite_seqP; exists s. Qed.
Hint Resolve finite_seq : core.

Lemma finite_fset {T : choiceType} (X : {fset T}) : finite_set [set` X].
Proof. by apply/finite_fsetP; exists X. Qed.
Hint Resolve finite_fset : core.

Lemma finite_finpred {T : finType} {pT : predType T} (P : pT) :
  finite_set [set` P].
Proof.
rewrite finite_seqP; exists (enum P).
by apply/seteqP; split=> x/=; rewrite mem_enum.
Qed.
Hint Extern 0 (finite_set [set` _]) => solve [apply: finite_finpred] : core.

Lemma finite_finset {T : finType} {X : set T} : finite_set X.
Proof.
by have -> : X = [set` mem X] by apply/seteqP; split=> x /=; rewrite ?inE.
Qed.
Hint Resolve finite_finset : core.

Lemma finite_set_countable T (A : set T) : finite_set A -> countable A.
Proof. by move=> /finite_setP[n /eq_countable->]. Qed.

Lemma infiniteP T (A : set T) : infinite_set A <-> [set: nat] #<= A.
Proof.
elim/Ppointed: T => T in A *.
  by rewrite !emptyE; split=> // /(congr1 (@^~ 0%N))/=; rewrite propeqE => -[].
split=> [Ainfinite| + /finite_setP[n eqAI]]; last first.
  rewrite (card_le_eqr eqAI) => le_nat_n.
  suff: `I_n.+1 #<= `I_n by rewrite card_le_II ltnn.
  exact: card_le_trans (subset_card_le _) le_nat_n.
have /all_sig2[f Af fX] : forall X : {fset T}, {x | x \in A & x \notin X}.
  move=> X; apply/sig2W; apply: contra_notP Ainfinite => nAX; apply/finite_fsetP.
  exists [fset x in X | x \in A]%fset; rewrite eqEsubset; split; last first.
    by move=> x/=; rewrite !inE => /andP[_]; rewrite inE.
  move=> x Ax /=; rewrite !inE/=; apply/andP; split; rewrite ?inE//.
  by apply: contra_notT nAX => xNX; exists x; rewrite ?inE.
do [under [forall x : {fset _}, _]eq_forall do rewrite inE] in Af *.
suff [g gE] : exists g : nat -> T,
    forall n, g n = f [fset g k | k in iota 0 n]%fset.
  have /Pinj[h hE] : {in setT &, injective g}.
    move=> i j _ _; apply: contra_eq; wlog lt_ij : i j / (i < j)%N => [hwlog|_].
    by case: ltngtP => // ij _; [|rewrite eq_sym];
       apply: hwlog=> //; rewrite lt_eqF//.
    rewrite [g j]gE; set X := (X in f X); have := fX X.
    by apply: contraNneq => <-; apply/imfsetP; exists i => //=; rewrite mem_iota.
  have/injPfun[i _] : {homo h : x / setT x >-> A x} by move=> i; rewrite -hE gE.
  by apply/pcard_leP; squash i.
pose g := fix g n k := if n isn't n'.+1 then f fset0
                       else f [fset g n' i | i in iota 0 k]%fset.
exists (fun n => g n n) => n.
suff {n} gn n k : (k <= n)%N -> g n k = f [fset g k k | k in iota 0 k]%fset.
  by rewrite gn//; congr f; apply/fsetP => k.
have [m] := ubnP n; elim: m n k => //= m IHm [|n] k /=.
  rewrite leqn0 => _ /eqP->/=.
  congr f; apply/fsetP => x; rewrite !inE; symmetry.
  by apply/imfsetP => /= -[].
rewrite ltnS => ltmn lekSn /=; congr f; apply/fsetP => i.
by apply/imfsetP/imfsetP => /= -[j]; rewrite mem_iota/= => jk ->;
   exists j; rewrite ?mem_iota//= ?add0n ?IHm//;
   by [rewrite (leq_trans jk)// (leq_trans lekSn)|rewrite -ltnS (leq_trans jk)].
Qed.

Lemma finite_setPn T (A : set T) : finite_set A <-> ~ ([set: nat] #<= A).
Proof. by rewrite -infiniteP notK. Qed.

Lemma card_le_finite T U (A : set T) (B : set U) :
  A #<= B -> finite_set B -> finite_set A.
Proof.
by move=> ?; rewrite !finite_setPn; apply: contra_not => /card_le_trans; apply.
Qed.

Lemma sub_finite_set T (A B : set T) : A `<=` B ->
  finite_set B -> finite_set A.
Proof. by move=> ?; apply/card_le_finite/subset_card_le. Qed.

Lemma finite_set_leP T (A : set T) : finite_set A <-> exists n, A #<= `I_n.
Proof.
split=> [[n /card_eqPle[]]|[n leAn]]; first by exists n.
by apply: card_le_finite leAn _; exists n.
Qed.

Lemma card_ge_preimage {T U} (B : set U) (f : T -> U) :
  {in f @^-1` B &, injective f} -> f @^-1` B #<= B.
Proof.
move=> /Pinj[g eqg]; rewrite -(card_le_eql (card_image g)) -eqg.
by apply: subset_card_le; apply: image_preimage_subset.
Qed.

Corollary finite_preimage {T U} (B : set U) (f : T -> U) :
  {in f @^-1` B &, injective f} -> finite_set B -> finite_set (f @^-1` B).
Proof. by move=> /card_ge_preimage fB; apply: card_le_finite. Qed.

Lemma eq_finite_set T U (A : set T) (B : set U) :
  A #= B -> finite_set A = finite_set B.
Proof.
move=> eqAB; apply/propeqP.
by split=> -[n Xn]; exists n; move: Xn; rewrite (card_eql eqAB).
Qed.

Lemma card_le_setD T (A B : set T) : A `\` B #<= A.
Proof. by apply: subset_card_le; rewrite setDE; apply: subIset; left. Qed.

Lemma finite_image T T' A (f : T -> T') : finite_set A -> finite_set (f @` A).
Proof. exact/card_le_finite/card_image_le. Qed.

Lemma finite_set1 T (x : T) : finite_set [set x].
Proof.
elim/Pchoice: T => T in x *.
by apply/finite_fsetP; exists (fset1 x); rewrite set_fset1.
Qed.
Hint Resolve finite_set1 : core.

Lemma finite_setD T (A B : set T) : finite_set A -> finite_set (A `\` B).
Proof. exact/card_le_finite/card_le_setD. Qed.

Lemma finite_setU T (A B : set T) :
  finite_set (A `|` B) = (finite_set A /\ finite_set B).
Proof.
pose fP := @finite_fsetP [choiceType of {classic T}]; rewrite propeqE; split.
  by move=> finAUB; split; apply: sub_finite_set finAUB.
by case=> /fP[X->]/fP[Y->]; apply/fP; exists (X `|` Y)%fset; rewrite set_fsetU.
Qed.

Lemma finite_set2 T (x y : T) : finite_set [set x; y].
Proof. by rewrite !finite_setU; split; apply: finite_set1. Qed.
Hint Resolve finite_set2 : core.

Lemma finite_set3 T (x y z : T) : finite_set [set x; y; z].
Proof. by rewrite !finite_setU; do !split; apply: finite_set1. Qed.
Hint Resolve finite_set3 : core.

Lemma finite_set4 T (x y z t : T) : finite_set [set x; y; z; t].
Proof. by rewrite !finite_setU; do !split; apply: finite_set1. Qed.
Hint Resolve finite_set4 : core.

Lemma finite_set5 T (x y z t u : T) : finite_set [set x; y; z; t; u].
Proof. by rewrite !finite_setU; do !split; apply: finite_set1. Qed.
Hint Resolve finite_set5 : core.

Lemma finite_set6 T (x y z t u v : T) : finite_set [set x; y; z; t; u; v].
Proof. by rewrite !finite_setU; do !split; apply: finite_set1. Qed.
Hint Resolve finite_set6 : core.

Lemma finite_set7 T (x y z t u v w : T) : finite_set [set x; y; z; t; u; v; w].
Proof. by rewrite !finite_setU; do !split; apply: finite_set1. Qed.
Hint Resolve finite_set7 : core.

Lemma finite_setI T (A B : set T) :
  (finite_set A \/ finite_set B) -> finite_set (A `&` B).
Proof.
by case; apply: contraPP; rewrite !infiniteP => /card_le_trans; apply;
   apply: subset_card_le.
Qed.

Lemma finite_setIl T (A B : set T) : finite_set A -> finite_set (A `&` B).
Proof. by move=> ?; apply: finite_setI; left. Qed.

Lemma finite_setIr T (A B : set T) : finite_set B -> finite_set (A `&` B).
Proof. by move=> ?; apply: finite_setI; right. Qed.

Lemma finite_setM T T' (A : set T) (B : set T') :
  finite_set A -> finite_set B -> finite_set (A `*` B).
Proof.
elim/Pchoice: T => T in A *; elim/Pchoice: T' => T' in B *.
move=> /finite_fsetP[{}A ->] /finite_fsetP[{}B ->].
apply/finite_fsetP; exists (A `*` B)%fset; apply/predeqP => x.
by split; rewrite /= inE => /andP.
Qed.

Lemma finite_image2 [aT bT rT : Type] [A : set aT] [B : set bT] (f : aT -> bT -> rT) :
  finite_set A -> finite_set B -> finite_set [set f x y | x in A & y in B]%classic.
Proof. by move=> fA fB; rewrite image2E; apply/finite_image/finite_setM. Qed.

Lemma finite_image11 [xT aT bT rT : Type] [X : set xT]
    (g : aT -> bT -> rT) (fa : xT -> aT) (fb : xT -> bT) :
    finite_set (fa @` X) -> finite_set (fb @` X) ->
  finite_set [set g (fa x) (fb x) | x in X]%classic.
Proof.
move=> /(finite_image2 g) /[apply]; apply: sub_finite_set; rewrite image2E.
by move=> r/= [x Xx <-]; exists (fa x, fb x) => //; split; exists x.
Qed.

Definition fset_set (T : choiceType) (A : set T) :=
  if pselect (finite_set A) is left Afin
  then projT1 (cid (finite_fsetP.1 Afin)) else fset0.

Lemma fset_setK (T : choiceType) (A : set T) : finite_set A ->
  [set` fset_set A] = A.
Proof. by rewrite /fset_set; case: pselect => // Afin _; case: cid. Qed.

Lemma in_fset_set (T : choiceType) (A : set T) : finite_set A ->
  fset_set A =i A.
Proof.
by move=> fA x; rewrite -[A in RHS]fset_setK//; apply/idP/idP; rewrite ?inE.
Qed.

Lemma fset_set0 {T : choiceType} : fset_set (set0 : set T) = fset0.
Proof.
by apply/fsetP=> x; rewrite in_fset_set ?inE//; apply/negP; rewrite inE.
Qed.

Lemma fset_set1 {T : choiceType} (x : T) : fset_set [set x] = [fset x]%fset.
Proof.
apply/fsetP=> y; rewrite in_fset_set ?inE//.
by apply/idP/idP; rewrite inE => /eqP.
Qed.

Lemma fset_setU {T : choiceType} (A B : set T) :
  finite_set A -> finite_set B ->
  fset_set (A `|` B) = (fset_set A `|` fset_set B)%fset.
Proof.
move=> fA fB; apply/fsetP=> x.
rewrite ?(inE, in_fset_set)//; last by rewrite finite_setU.
by apply/idP/orP; rewrite ?inE.
Qed.

Lemma fset_setI {T : choiceType} (A B : set T) :
  finite_set A -> finite_set B ->
  fset_set (A `&` B) = (fset_set A `&` fset_set B)%fset.
Proof.
move=> fA fB; apply/fsetP=> x.
rewrite ?(inE, in_fset_set)//; last by apply: finite_setI; left.
by apply/idP/andP; rewrite ?inE.
Qed.

Lemma fset_setU1 {T : choiceType} (x : T) (A : set T) :
  finite_set A -> fset_set (x |` A) = (x |` fset_set A)%fset.
Proof. by move=> fA; rewrite fset_setU// fset_set1. Qed.

Lemma fset_setD {T : choiceType} (A B : set T) :
  finite_set A -> finite_set B ->
  fset_set (A `\` B) = (fset_set A `\` fset_set B)%fset.
Proof.
move=> fA fB; apply/fsetP=> x.
rewrite ?(inE, in_fset_set)//; last exact: finite_setD.
by apply/idP/andP; rewrite ?inE => -[]; rewrite ?notin_set.
Qed.

Lemma fset_setD1 {T : choiceType} (x : T) (A : set T) :
  finite_set A -> fset_set (A `\ x) = (fset_set A `\ x)%fset.
Proof. by move=> fA; rewrite fset_setD// fset_set1. Qed.

Lemma fset_setM {T1 T2 : choiceType} (A : set T1) (B : set T2) :
    finite_set A -> finite_set B ->
  fset_set (A `*` B) = (fset_set A `*` fset_set B)%fset.
Proof.
move=> Afin Bfin; have ABfin : finite_set (A `*` B) by apply: finite_setM.
apply/fsetP => i; apply/idP/idP; rewrite !(inE, in_fset_set)//=.
  by move=> [/mem_set-> /mem_set->].
by move=> /andP[]; rewrite !inE.
Qed.

Definition fst_fset (T1 T2 : choiceType) (A : {fset (T1 * T2)}) : {fset T1} :=
  [fset x.1 | x in A]%fset.
Definition snd_fset (T1 T2 : choiceType) (A : {fset (T1 * T2)}) : {fset T2} :=
  [fset x.2 | x in A]%fset.
Notation "A .`1" := (fst_fset A) : fset_scope.
Notation "A .`2" := (snd_fset A) : fset_scope.

Lemma finite_set_fst (T1 T2 : choiceType) (A : set (T1 * T2)) :
  finite_set A -> finite_set A.`1.
Proof.
move=> /finite_fsetP[B A_B]; apply/finite_fsetP; exists (B.`1)%fset.
by apply/seteqP; split=> [x/= [y]|_/= /imfsetP[[x1 x2]/= +] ->]; rewrite A_B;
  [move=> xyB; apply/imfsetP; exists (x, y)|move=> ?; exists x2].
Qed.

Lemma finite_set_snd (T1 T2 : choiceType) (A : set (T1 * T2)) :
  finite_set A -> finite_set A.`2.
Proof.
move=> /finite_fsetP[B A_B]; apply/finite_fsetP; exists (B.`2)%fset.
apply/seteqP; split=> [y/= [x]|_/= /imfsetP[[x1 x2]/= +] ->]; rewrite A_B;
  by [move=> xyB; apply/imfsetP; exists (x, y)|move=> ?; exists x1].
Qed.

Lemma bigcup_finite {I T} (D : set I) (F : I -> set T) :
    finite_set D -> (forall i, D i -> finite_set (F i)) ->
  finite_set (\bigcup_(i in D) F i).
Proof.
elim/Pchoice: I => I in D F *.
elim/Ppointed: T => T in F *; first by rewrite emptyE.
move=> Dfin Ffin; pose G (i : fset_set D) := fset_set (F (val i)).
suff: (\bigcup_(i in D) F i #<= [set: {i & G i}])%card.
  by move=> /card_le_finite; apply; apply: finite_finset.
apply/pcard_geP/surjPex.
exists (fun (k : {i : fset_set D & G i}) => val (projT2 k)).
move=> y [i Di Fky]/=.
have Dk : i \in fset_set D by rewrite in_fset_set// inE.
pose k : fset_set D := [` Dk]%fset.
have Gy : y \in G k by rewrite in_fset_set ?inE//; apply: Ffin.
by exists (Tagged G [` Gy]%fset).
Qed.

Lemma finite_setMR (T T' : choiceType) (A : set T) (B : T -> set T') :
  finite_set A -> (forall x, A x -> finite_set (B x)) -> finite_set (A `*`` B).
Proof.
move=> Afin Bfin; rewrite -bigcupM1l.
by apply: bigcup_finite => // i Ai; apply/finite_setM/Bfin.
Qed.

Lemma finite_setML (T T' : choiceType) (A : T' -> set T) (B : set T') :
  (forall x, B x -> finite_set (A x)) -> finite_set B -> finite_set (A ``*` B).
Proof.
move=> Afin Bfin; rewrite -bigcupM1r.
by apply: bigcup_finite => // i Ai; apply/finite_setM=> //; apply: Afin.
Qed.

Lemma fset_set_II n : fset_set `I_n = [fset val i | i in 'I_n]%fset.
Proof.
apply/fsetP => i; rewrite /= ?inE in_fset_set//.
apply/idP/imfsetP; rewrite ?inE/=.
  by move=> lt_in; exists (Ordinal lt_in).
by move=> [j _ ->].
Qed.

Lemma set_fsetK (T : choiceType) (A : {fset T}) : fset_set [set` A] = A.
Proof.
apply/fsetP => x; rewrite in_fset_set//=.
by apply/idP/idP; rewrite ?inE.
Qed.

Lemma fset_set_inj {T : choiceType} (A B : set T) :
  finite_set A -> finite_set B -> fset_set A = fset_set B -> A = B.
Proof. by move=> Afin Bfin /(congr1 pred_set); rewrite !fset_setK. Qed.

Lemma bigsetU_fset_set T (I : choiceType) (A : set I) (F : I -> set T) :
  finite_set A -> \big[setU/set0]_(i <- fset_set A) F i =\bigcup_(i in A) F i.
Proof.
move=> finA; rewrite -bigcup_fset /fset_set; case: pselect => [{}finA|//].
apply/seteqP; split=> [x [i /=]|x [i Ai Fix]].
  by case: cid => /= B -> iB Fix; exists i.
by exists i => //; case: cid => // B AB /=; move: Ai; rewrite AB.
Qed.

#[deprecated(note="Use -bigsetU_fset_set instead")]
Lemma bigcup_fset_set T (I : choiceType) (A : set I) (F : I -> set T) :
  finite_set A -> \bigcup_(i in A) F i = \big[setU/set0]_(i <- fset_set A) F i.
Proof. by move=> /bigsetU_fset_set->. Qed.

Lemma bigsetU_fset_set_cond T (I : choiceType) (A : set I) (F : I -> set T)
    (P : pred I) : finite_set A ->
  \big[setU/set0]_(i <- fset_set A | P i) F i = \bigcup_(i in A `&` P) F i.
Proof.
by move=> *; rewrite bigcup_mkcondr big_mkcond -bigcup_fset_set ?mem_setE.
Qed.

#[deprecated(note="Use -bigsetU_fset_set_cond instead")]
Lemma bigcup_fset_set_cond T (I : choiceType) (A : set I) (F : I -> set T)
    (P : pred I) : finite_set A ->
  \bigcup_(i in A `&` P) F i = \big[setU/set0]_(i <- fset_set A | P i) F i.
Proof. by move=> /bigsetU_fset_set_cond->. Qed.

Lemma bigsetI_fset_set T (I : choiceType) (A : set I) (F : I -> set T) :
  finite_set A -> \big[setI/setT]_(i <- fset_set A) F i =\bigcap_(i in A) F i.
Proof.
by move=> *; apply: setC_inj; rewrite setC_bigcap setC_bigsetI bigsetU_fset_set.
Qed.

#[deprecated(note="Use -bigsetI_fset_set instead")]
Lemma bigcap_fset_set T (I : choiceType) (A : set I) (F : I -> set T) :
  finite_set A -> \bigcap_(i in A) F i = \big[setI/setT]_(i <- fset_set A) F i.
Proof. by move=> /bigsetI_fset_set->. Qed.

Lemma bigsetI_fset_set_cond T (I : choiceType) (A : set I) (F : I -> set T)
    (P : pred I) : finite_set A ->
  \big[setI/setT]_(i <- fset_set A | P i) F i = \bigcap_(i in A `&` P) F i.
Proof.
by move=> *; rewrite bigcap_mkcondr big_mkcond -bigcap_fset_set ?mem_setE.
Qed.

Lemma super_bij T U (X A : set T) (Y B : set U) (f : {bij X >-> Y}) :
  X `<=` A -> Y `<=` B -> A `\` X #= B `\` Y ->
  exists g : {bij A >-> B}, {in X, g =1 f}.
Proof.
elim/Ppointed: U => U in Y B f *.
  rewrite !emptyE in f * => XA _; rewrite setD_eq0 => AX.
  by suff /seteqP->// : A `<=>` X by exists f.
move=> XA YB /pcard_eqP[g].
rewrite -(joinIB X A) -(joinIB Y B) !meetEset.
have /disj_set2P AX : (A `&` X) `&` (A `\` X) = set0 by apply: meetIB.
have /disj_set2P BY : (B `&` Y) `&` (B `\` Y) = set0 by apply: meetIB.
rewrite !(setIidr XA) !(setIidr YB) in AX BY *.
by exists [bij of glue AX BY f g] => x /= xX; rewrite glue1.
Qed.

Lemma card_eq_fsetP {T : choiceType} {A : {fset T}} {n} :
  reflect (#|` A| = n) ([set` A] #= `I_n).
Proof.
elim/choicePpointed: T => T in A *.
  rewrite empty_eq0 card_eq_sym (card_eqr (card_eq00 _ nat)) -II0.
  apply: (iffP card_eq_II) => [->|].
    by apply/eqP; rewrite cardfs_eq0; apply/eqP/fsetP=> i; have := no i.
  by have -> : A = fset0; [apply/fsetP=> i; have := no i | rewrite cardfs0].
rewrite (card_eqr card_II) card_eq_sym.
apply: (iffP pcard_eqP) => [[f]|]; last first.
  rewrite cardfE => eqAn.
  by squash (set_val \o finset_val \o enum_val \o cast_ord (esym eqAn)).
suff -> : A = [fset f i | i in 'I_n]%fset.
  by rewrite card_imfset ?size_enum_ord//=; apply: (in2TT inj).
apply/fsetP => x; apply/idP/imfsetP => /= [xA|[i _ ->]].
  by have [i _ <-] := 'surj_f xA; exists i.
by have /(_ i I) := 'funS_f.
Qed.

Lemma card_IID {n k} : `I_n `\` `I_k #= `I_(n - k)%N.
Proof.
have /orP[|kn] := leq_total k n; last first.
  rewrite (eqP kn) II0 card_eq0 eq_opE -subset0 => i/= [ltin].
  by apply; apply: leq_trans kn.
move=> /subnKC{1}<-; move: (n - k)%N => m.
apply/card_esym/pcard_eqP/bijPex; exists (addn k); split.
- by move=> i leim /=; rewrite ltn_add2l leim ltnNge leq_addr.
- by move=> i j _ _ /addnI.
- move=> i [/= ikm /negP]; rewrite -leqNgt => leki.
  by exists (i - k)%N; rewrite ?ltn_subLR // subnKC.
Qed.

Lemma finite_set_bij T (A : set T) n S : A != set0 ->
    A #= `I_n -> S `<=` A ->
  exists (f : {bij `I_n >-> A}) k, (k <= n)%N /\ `I_n `&` (f @^-1` S) = `I_k.
Proof.
elim/Ppointed: T => T in A S *; first by rewrite !emptyE eqxx.
move=> AN0 An SA; have [k kn Sk] : exists2 k, (k <= n)%N & S #= `I_k.
  have /finite_setP[k Sk]: finite_set S by apply: sub_finite_set SA _; exists n.
  exists k => //; rewrite -card_le_II.
  by rewrite -(card_le_eqr An) -(card_le_eql Sk); apply: subset_card_le.
have /card_esym/ppcard_eqP[f] := Sk.
have eqAS : A `\` S #= `I_n `\` `I_k.
  have An' := An; have Sk' := Sk.
  do [have /finite_fsetP[{An'}A ->] : finite_set A by exists n] in An AN0 SA *.
  do [have /finite_fsetP[{Sk'}S ->] : finite_set S by exists k] in Sk f SA *.
  have [/card_eq_fsetP {}An /card_eq_fsetP {}Sk] := (An, Sk).
  rewrite -set_fsetD (card_eqr card_IID); apply/card_eq_fsetP.
  by rewrite cardfsD (fsetIidPr _) ?An ?Sk //; apply/fsubsetP.
case: (super_bij [bij of f^-1] SA _ eqAS) => [x /= /leq_trans->// | g].
have [{}g ->] := pPbij 'bij_g => /= gE.
exists [bij of g^-1], k; split=> //=; rewrite -inv_sub_image //= invV.
by under eq_imagel do rewrite /= gE ?inE//; rewrite image_eq.
Qed.

#[deprecated(note="use countable0 instead")]
Notation countable_set0 := countable0.

Lemma countable1 T (x : T) : countable [set x].
Proof. exact: finite_set_countable. Qed.
Hint Resolve countable1 : core.

Lemma countable_fset (T : choiceType) (X : {fset T}) : countable [set` X].
Proof. exact: finite_set_countable. Qed.
Hint Resolve countable_fset : core.

Lemma countable_finpred (T : finType) (pT : predType T) (P : pT) : countable [set` P].
Proof. exact: finite_set_countable. Qed.
Hint Extern 0 (is_true (countable [set` _])) => solve [apply: countable_finpred] : core.

Lemma eq_card_nat T (A : set T):
  countable A -> ~ finite_set A -> A #= [set: nat].
Proof. by move=> Acnt /infiniteP leNA; rewrite card_eq_le leNA andbT. Qed.

Lemma infinite_nat : ~ finite_set [set: nat].
Proof. exact/infiniteP/card_lexx. Qed.

Lemma infinite_prod_nat : infinite_set [set: nat * nat].
Proof.
by apply/infiniteP/pcard_leTP/injPex; exists (pair 0%N) => // m n _ _ [].
Qed.

Lemma card_nat2 : [set: nat * nat] #= [set: nat].
Proof. exact/eq_card_nat/infinite_prod_nat/countableP. Qed.

Canonical rat_pointedType := PointedType rat 0.

Lemma infinite_rat : infinite_set [set: rat].
Proof.
apply/infiniteP/pcard_leTP/injPex; exists (GRing.natmul 1) => // m n _ _.
exact/Num.Theory.mulrIn/oner_neq0.
Qed.

Lemma card_rat : [set: rat] #= [set: nat].
Proof. exact/eq_card_nat/infinite_rat/countableP. Qed.

Lemma choicePcountable {T : choiceType} : countable [set: T] ->
  {T' : countType | T = T' :> Type}.
Proof.
move=> /pcard_leP/unsquash f.
by exists (CountType T (CountMixin (in1TT 'funoK_f))).
Qed.

Lemma eqPcountable {T : eqType} : countable [set: T] ->
  {T' : countType | T = T' :> Type}.
Proof. by elim/eqPchoice: T => T /choicePcountable. Qed.

Lemma Pcountable {T : Type} : countable [set: T] ->
  {T' : countType | T = T' :> Type}.
Proof. by elim/Pchoice: T => T /choicePcountable. Qed.

Lemma bigcup_countable {I T} (D : set I) (F : I -> set T) :
    countable D -> (forall i, D i -> countable (F i)) ->
  countable (\bigcup_(i in D) F i).
Proof.
elim/Ppointed: T => T in F *; first by rewrite emptyE.
rewrite -(eq_countable (card_setT _)) => cD cF; rewrite bigcup_set_type.
set G := (fun i : D => F (val i)).
have {cF}cG i : countable (G i) by apply: cF; apply: set_valP.
move: (D : Type) cD G cG => {F I}_ /Pcountable[{}D ->] G cG.
suff: (\bigcup_i G i #<= [set: {i & G i}])%card.
  have cGT i : countable [set: G i] by rewrite (eq_countable (card_setT _)).
  have /all_sig[H GE] := fun i => Pcountable (cGT i).
  by move=> /sub_countable->//; rewrite (eq_fun GE).
apply/pcard_geP/surjPex; exists (fun (k : {i & G i}) => val (projT2 k)).
by move=> x [i _] Gix/=; exists (Tagged G (SigSub (mem_set Gix))).
Qed.

Lemma countableMR T T' (A : set T) (B : T -> set T') :
  countable A -> (forall i, A i -> countable (B i)) -> countable (A `*`` B).
Proof.
elim/Ppointed: T => T in A B *; first by rewrite emptyE -bigcupM1l bigcup_set0.
elim/Ppointed: T' => T' in B *.
  by rewrite -bigcupM1l bigcup0// => i; rewrite emptyE setM0.
move=> Ac Bc; rewrite -bigcupM1l bigcup_countable// => i Ai.
have /ppcard_leP[f] := Bc i Ai; apply/pcard_geP/surjPex.
exists (fun k => (i, f^-1%FUN k)) => -[_ j]/= [-> dj].
by exists (f j) => //=; rewrite funK ?inE.
Qed.

Lemma countableM T1 T2 (D1 : set T1) (D2 : set T2) :
  countable D1 -> countable D2 -> countable (D1 `*` D2).
Proof. by move=> D1c D2c; apply: countableMR (fun _ _ => D2c). Qed.

Lemma countableML T T' (A : T' -> set T) (B : set T') :
  countable B -> (forall i, B i -> countable (A i)) -> countable (A ``*` B).
Proof.
move=> Bc Ac; rewrite -bigcupM1r; apply: bigcup_countable => // i Bi.
by apply: countableM => //; apply: Ac.
Qed.

Lemma infiniteMRl T T' (A : set T) (B : T -> set T') :
  infinite_set A -> (forall i, B i !=set0) -> infinite_set (A `*`` B).
Proof.
move=> /infiniteP/pcard_geP[f] /(_ _)/cid-/all_sig[b Bb].
apply/infiniteP/pcard_geP/surjPex; exists (fun x => f x.1).
by move=> i iT; have [a Aa fa] := 'oinvP_f iT; exists (a, b a) => /=.
Qed.

Lemma cardMR_eq_nat T T' (A : set T) (B : T -> set T') :
    (A #= [set: nat] -> (forall i, countable (B i) /\ B i !=set0) ->
   A `*`` B #= [set: nat])%card.
Proof.
rewrite !card_eq_le => /andP[Acnt /infiniteP Ainfty] /all_and2[Bcnt Bn0].
by rewrite [(_ #<= _)%card]countableMR//=; apply/infiniteP/infiniteMRl.
Qed.
