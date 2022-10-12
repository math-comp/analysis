(* mathcomp analysis (c) 2022 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrnum interval.
Require Import boolp classical_sets.

(***************************)
(* MathComp 1.15 additions *)
(***************************)

(******************************************************************************)
(* This files contains lemmas and definitions missing from MathComp.          *)
(*                                                                            *)
(*                oflit f := Some \o f                                        *)
(*          pred_oapp T D := [pred x | oapp (mem D) false x]                  *)
(*                 f \* g := fun x => f x * g x                               *)
(*                   \- f := fun x => - f x                                   *)
(*     lteBSide, bnd_simp == multirule to simplify inequalities between       *)
(*                           interval bounds                                  *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "f \* g" (at level 40, left associativity).
Reserved Notation "f \- g" (at level 50, left associativity).
Reserved Notation "\- f"  (at level 35, f at level 35).

Lemma all_sig2_cond {I : Type} {T : Type} (D : pred I)
   (P Q : I -> T -> Prop) : T ->
    (forall x : I, D x -> {y : T | P x y & Q x y}) ->
  {f : forall x : I, T | forall x : I, D x -> P x (f x) & forall x : I, D x -> Q x (f x)}.
Proof.
by move=> /all_sig_cond/[apply]-[f Pf]; exists f => i Di; have [] := Pf i Di.
Qed.

Definition olift aT rT (f : aT -> rT) := Some \o f.

Lemma oapp_comp aT rT sT (f : aT -> rT) (g : rT -> sT) x :
  oapp (g \o f) x =1 (@oapp _ _)^~ x g \o omap f.
Proof. by case. Qed.

Lemma olift_comp aT rT sT (f : aT -> rT) (g : rT -> sT) :
  olift (g \o f) = olift g \o f.
Proof. by []. Qed.

Lemma compA {A B C D : Type} (f : B -> A) (g : C -> B) (h : D -> C) :
  f \o (g \o h) = (f \o g) \o h.
Proof. by []. Qed.

Lemma can_in_pcan [rT aT : Type] (A : {pred aT}) [f : aT -> rT] [g : rT -> aT] :
  {in A, cancel f g} -> {in A, pcancel f (fun y : rT => Some (g y))}.
Proof. by move=> fK x Ax; rewrite fK. Qed.

Lemma pcan_in_inj [rT aT : Type] [A : {pred aT}] [f : aT -> rT] [g : rT -> option aT] :
  {in A, pcancel f g} -> {in A &, injective f}.
Proof. by move=> fK x y Ax Ay /(congr1 g); rewrite !fK// => -[]. Qed.

Definition pred_oapp T (D : {pred T}) : pred (option T) :=
  [pred x | oapp (mem D) false x].

Lemma ocan_in_comp [A B C : Type] (D : {pred B}) (D' : {pred C})
    [f : B -> option A] [h : C -> option B]
    [f' : A -> B] [h' : B -> C] :
  {homo h : x / x \in D' >-> x \in pred_oapp D} ->
  {in D, ocancel f f'} -> {in D', ocancel h h'} ->
  {in D', ocancel (obind f \o h) (h' \o f')}.
Proof.
move=> hD fK hK c cD /=; rewrite -[RHS]hK/=; case hcE : (h c) => [b|]//=.
have bD : b \in D by have := hD _ cD; rewrite hcE inE.
by rewrite -[b in RHS]fK; case: (f b) => //=; have /hK := cD; rewrite hcE.
Qed.

Lemma pred_oappE {T : Type} (D : {pred T}) :
  pred_oapp D = mem (some @` D)%classic.
Proof.
apply/funext=> -[x|]/=; apply/idP/idP; rewrite /pred_oapp/= inE //=.
- by move=> xD; exists x.
- by move=> [// + + [<-]].
- by case.
Qed.

Lemma pred_oapp_set {T : Type} (D : set T) :
  pred_oapp (mem D) = mem (some @` D)%classic.
Proof.
by rewrite pred_oappE; apply/funext => x/=; apply/idP/idP; rewrite ?inE;
   move=> [y/= ]; rewrite ?in_setE; exists y; rewrite ?in_setE.
Qed.

Lemma eqbRL (b1 b2 : bool) : b1 = b2 -> b2 -> b1.
Proof. by move->. Qed.

Definition mul_fun T (R : ringType) (f g : T -> R) x := (f x * g x)%R.
Notation "f \* g" := (mul_fun f g) : ring_scope.
Arguments mul_fun {T R} _ _ _ /.

Definition opp_fun T (R : zmodType) (f : T -> R) x := (- f x)%R.
Notation "\- f" := (opp_fun f) : ring_scope.
Arguments opp_fun {T R} _ _ /.

Coercion pair_of_interval T (I : interval T) : itv_bound T * itv_bound T :=
  let: Interval b1 b2 := I in (b1, b2).

Import Order.TTheory GRing.Theory Num.Theory.

Section itv_simp.
Variables (d : unit) (T : porderType d).
Implicit Types (x y : T) (b : bool).

Lemma ltBSide x y b b' :
  ((BSide b x < BSide b' y) = (x < y ?<= if b && ~~ b'))%O.
Proof. by []. Qed.

Lemma leBSide x y b b' :
  ((BSide b x <= BSide b' y) = (x < y ?<= if b' ==> b))%O.
Proof. by []. Qed.

Definition lteBSide := (ltBSide, leBSide).

Let BLeft_ltE x y b : (BSide b x < BLeft y)%O = (x < y)%O.
Proof. by case: b. Qed.
Let BRight_leE x y b : (BSide b x <= BRight y)%O = (x <= y)%O.
Proof. by case: b. Qed.
Let BRight_BLeft_leE x y : (BRight x <= BLeft y)%O = (x < y)%O.
Proof. by []. Qed.
Let BLeft_BRight_ltE x y : (BLeft x < BRight y)%O = (x <= y)%O.
Proof. by []. Qed.
Let BRight_BSide_ltE x y b : (BRight x < BSide b y)%O = (x < y)%O.
Proof. by case: b. Qed.
Let BLeft_BSide_leE x y b : (BLeft x <= BSide b y)%O = (x <= y)%O.
Proof. by case: b. Qed.
Let BSide_ltE x y b : (BSide b x < BSide b y)%O = (x < y)%O.
Proof. by case: b. Qed.
Let BSide_leE x y b : (BSide b x <= BSide b y)%O = (x <= y)%O.
Proof. by case: b. Qed.
Let BInfty_leE a : (a <= BInfty T false)%O. Proof. by case: a => [[] a|[]]. Qed.
Let BInfty_geE a : (BInfty T true <= a)%O. Proof. by case: a => [[] a|[]]. Qed.
Let BInfty_le_eqE a : (BInfty T false <= a)%O = (a == BInfty T false).
Proof. by case: a => [[] a|[]]. Qed.
Let BInfty_ge_eqE a : (a <= BInfty T true)%O = (a == BInfty T true).
Proof. by case: a => [[] a|[]]. Qed.
Let BInfty_ltE a : (a < BInfty T false)%O = (a != BInfty T false).
Proof. by case: a => [[] a|[]]. Qed.
Let BInfty_gtE a : (BInfty T true < a)%O = (a != BInfty T true).
Proof. by case: a => [[] a|[]]. Qed.
Let BInfty_ltF a : (BInfty T false < a)%O = false.
Proof. by case: a => [[] a|[]]. Qed.
Let BInfty_gtF a : (a < BInfty T true)%O = false.
Proof. by case: a => [[] a|[]]. Qed.
Let BInfty_BInfty_ltE : (BInfty T true < BInfty T false)%O. Proof. by []. Qed.

Lemma ltBRight_leBLeft (a : itv_bound T) (r : T) :
  (a < BRight r)%O = (a <= BLeft r)%O.
Proof. by move: a => [[] a|[]]. Qed.
Lemma leBRight_ltBLeft (a : itv_bound T) (r : T) :
  (BRight r <= a)%O = (BLeft r < a)%O.
Proof. by move: a => [[] a|[]]. Qed.

Definition bnd_simp := (BLeft_ltE, BRight_leE,
  BRight_BLeft_leE, BLeft_BRight_ltE,
  BRight_BSide_ltE, BLeft_BSide_leE, BSide_ltE, BSide_leE,
  BInfty_leE, BInfty_geE, BInfty_BInfty_ltE,
  BInfty_le_eqE, BInfty_ge_eqE, BInfty_ltE, BInfty_gtE, BInfty_ltF, BInfty_gtF,
  @lexx _ T, @ltxx _ T, @eqxx T).

Lemma itv_splitU1 (a : itv_bound T) (x : T) : (a <= BLeft x)%O ->
  Interval a (BRight x) =i [predU1 x & Interval a (BLeft x)].
Proof.
move=> ax z; rewrite !inE/= !subitvE ?bnd_simp//= lt_neqAle.
by case: (eqVneq z x) => [->|]//=; rewrite lexx ax.
Qed.

Lemma itv_split1U (a : itv_bound T) (x : T) : (BRight x <= a)%O ->
  Interval (BLeft x) a =i [predU1 x & Interval (BRight x) a].
Proof.
move=> ax z; rewrite !inE/= !subitvE ?bnd_simp//= lt_neqAle.
by case: (eqVneq z x) => [->|]//=; rewrite lexx ax.
Qed.

End itv_simp.

Definition miditv (R : numDomainType) (i : interval R) : R :=
  match i with
  | Interval (BSide _ a) (BSide _ b) => (a + b) / 2%:R
  | Interval -oo%O (BSide _ b) => b - 1
  | Interval (BSide _ a) +oo%O => a + 1
  | Interval -oo%O +oo%O => 0
  | _ => 0
  end.

Section miditv_lemmas.
Variable R : numFieldType.
Implicit Types i : interval R.

Lemma mem_miditv i : (i.1 < i.2)%O -> miditv i \in i.
Proof.
move: i => [[ba a|[]] [bb b|[]]] //= ab; first exact: mid_in_itv.
  by rewrite !in_itv -lteif_subl_addl subrr lteif01.
by rewrite !in_itv lteif_subl_addr -lteif_subl_addl subrr lteif01.
Qed.

Lemma miditv_le_left i b : (i.1 < i.2)%O -> (BSide b (miditv i) <= i.2)%O.
Proof.
case: i => [x y] lti; have := mem_miditv lti; rewrite inE => /andP[_ ].
by apply: le_trans; rewrite !bnd_simp.
Qed.

Lemma miditv_ge_right i b : (i.1 < i.2)%O -> (i.1 <= BSide b (miditv i))%O.
Proof.
case: i => [x y] lti; have := mem_miditv lti; rewrite inE => /andP[+ _].
by move=> /le_trans; apply; rewrite !bnd_simp.
Qed.

End miditv_lemmas.

Section itv_porderType.
Variables (d : unit) (T : orderType d).
Implicit Types (a : itv_bound T) (x y : T) (i j : interval T) (b : bool).

Lemma predC_itvl a : [predC Interval -oo%O a] =i Interval a +oo%O.
Proof.
case: a => [b x|[]//] y.
by rewrite !inE !subitvE/= bnd_simp andbT !lteBSide/= lteifNE negbK.
Qed.

Lemma predC_itvr a : [predC Interval a +oo%O] =i Interval -oo%O a.
Proof. by move=> y; rewrite inE/= -predC_itvl negbK. Qed.

Lemma predC_itv i : [predC i] =i [predU Interval -oo%O i.1 & Interval i.2 +oo%O].
Proof.
case: i => [a a']; move=> x; rewrite inE/= itv_splitI negb_and.
by symmetry; rewrite inE/= -predC_itvl -predC_itvr.
Qed.

End itv_porderType.

Import Num.Theory.

Lemma sumr_le0 (R : numDomainType) I (r : seq I) (P : pred I) (F : I -> R) :
  (forall i, P i -> F i <= 0)%R -> (\sum_(i <- r | P i) F i <= 0)%R.
Proof. by move=> F0; elim/big_rec : _ => // i x Pi; apply/ler_naddl/F0. Qed.

(**********************************)
(* End of MathComp 1.15 additions *)
(**********************************)
