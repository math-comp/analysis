(* Borrowed from Stdlib.Logic.EqdepFacts and Stdlib.Logic.Eqdep_dec *)

Import EqNotations.

Section Dependent_Equality.

Variables (U : Type) (P : U -> Type).

Inductive eq_dep (p : U) (x : P p) : forall q : U, P q -> Prop :=
  eq_dep_intro : eq_dep p x p x.

Lemma eq_dep_sym (p q : U) (x : P p) (y : P q) :
  eq_dep p x q y -> eq_dep q y p x.
Proof. destruct 1; auto; apply eq_dep_intro. Qed.

Inductive eq_dep1 (p : U) (x : P p) (q : U) (y : P q) : Prop :=
  eq_dep1_intro : forall h : q = p, x = rew h in y -> eq_dep1 p x q y.

Lemma eq_dep_dep1 (p q : U) (x : P p) (y : P q) :
  eq_dep p x q y -> eq_dep1 p x q y.
Proof.
revert p q x y; intros p; destruct 1.
apply eq_dep1_intro with (eq_refl p); simpl; trivial.
Qed.

End Dependent_Equality.

Section Equivalences.

Variable U : Type.

Definition Eq_rect_eq_on (p : U) (Q : U -> Type) (x : Q p) :=
  forall (h : p = p), x = eq_rect p Q x p h.
Definition Eq_rect_eq := forall p Q x, Eq_rect_eq_on p Q x.

Definition Eq_dep_eq_on (P : U -> Type) (p : U) (x : P p) :=
  forall (y : P p), eq_dep _ _ p x p y -> x = y.
Definition Eq_dep_eq := forall P p x, Eq_dep_eq_on P p x.

Definition Streicher_K_on_ (x : U) (P : x = x -> Prop) :=
  P (eq_refl x) -> forall p : x = x, P p.
Definition Streicher_K_ := forall x P, Streicher_K_on_ x P.

Lemma eq_rect_eq_on__eq_dep1_eq_on (p : U) (P : U -> Type) (y : P p) :
  Eq_rect_eq_on p P y -> forall (x : P p), eq_dep1 _ _ p x p y -> x = y.
Proof. intro ere; simple destruct 1; intro; rewrite <-ere; auto. Qed.

Lemma eq_rect_eq__eq_dep1_eq :
  Eq_rect_eq -> forall (P:U->Type) (p:U) (x y:P p), eq_dep1 _ _ p x p y -> x = y.
Proof (fun eq_rect_eq P p y x =>
  @eq_rect_eq_on__eq_dep1_eq_on p P x (eq_rect_eq p P x) y).

Lemma eq_rect_eq_on__eq_dep_eq_on (p : U) (P : U -> Type) (x : P p) :
  Eq_rect_eq_on p P x -> Eq_dep_eq_on P p x.
Proof.
intros eq_rect_eq; red; intros y H.
symmetry; apply (eq_rect_eq_on__eq_dep1_eq_on _ _ _ eq_rect_eq).
apply eq_dep_sym in H; apply eq_dep_dep1; trivial.
Qed.
Lemma eq_rect_eq__eq_dep_eq : Eq_rect_eq -> Eq_dep_eq.
Proof (fun eq_rect_eq P p x y =>
  @eq_rect_eq_on__eq_dep_eq_on p P x (eq_rect_eq p P x) y).

Lemma Streicher_K_on__eq_rect_eq_on (p : U) (P : U -> Type) (x : P p) :
  Streicher_K_on_ p (fun h => x = rew -> [P] h in x) -> Eq_rect_eq_on p P x.
Proof. intro Streicher_K; red; intros; apply Streicher_K; reflexivity. Qed.
Lemma Streicher_K__eq_rect_eq : Streicher_K_ -> Eq_rect_eq.
Proof.
exact (fun Streicher_K p P x =>
  @Streicher_K_on__eq_rect_eq_on p P x (Streicher_K p _)).
Qed.
End Equivalences.

Set Implicit Arguments.

Section EqdepDec.

Variable A : Type.

Let comp (x y y' : A) (eq1 : x = y) (eq2 : x = y') : y = y' :=
  eq_ind _ (fun a => a = y') eq2 _ eq1.

Remark trans_sym_eq (x y : A) (u : x = y) : comp u u = eq_refl y.
Proof. now case u. Qed.

Variables (x : A) (eq_dec : forall y : A, x = y \/ x <> y).

Let nu (y:A) (u:x = y) : x = y :=
  match eq_dec y with
  | or_introl eqxy => eqxy
  | or_intror neqxy => False_ind _ (neqxy u)
  end.

#[local] Lemma nu_constant (y : A) (u v : x = y) : nu u = nu v.
Proof.
now unfold nu; destruct (eq_dec y) as [Heq|Hneq]; [reflexivity|case Hneq].
Qed.

Let nu_inv (y : A) (v : x = y) : x = y := comp (nu (eq_refl x)) v.

Remark nu_left_inv_on (y:A) (u:x = y) : nu_inv (nu u) = u.
Proof. case u; unfold nu_inv; apply trans_sym_eq. Qed.

Theorem eq_proofs_unicity_on (y : A) (p1 p2 : x = y) : p1 = p2.
Proof.
elim (nu_left_inv_on p1).
elim (nu_left_inv_on p2).
elim nu_constant with y p1 p2.
reflexivity.
Qed.

Theorem K_dec_on (P : x = x -> Prop) (H : P (eq_refl x)) (p : x = x) : P p.
Proof. now elim eq_proofs_unicity_on with x (eq_refl x) p. Qed.

End EqdepDec.

Theorem K_dec A (eq_dec : forall x y : A, x = y \/ x <> y) (x : A) :
  forall P : x = x -> Prop, P (eq_refl x) -> forall p : x = x, P p.
Proof. exact (@K_dec_on A x (eq_dec x)). Qed.

Section Eq_dec.

Variables (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}).

Theorem K_dec_type (x : A) (P : x = x -> Prop) (H : P (eq_refl x)) (p : x = x) :
  P p.
Proof.
elim p using K_dec; [|now trivial].
now intros x0 y; case (eq_dec x0 y); [left|right].
Qed.

Theorem eq_rect_eq_dec : forall (p : A) (Q : A -> Type) (x : Q p) (h : p = p),
  x = eq_rect p Q x p h.
Proof. exact (Streicher_K__eq_rect_eq A K_dec_type). Qed.

Unset Implicit Arguments.

Lemma eq_sigT_eq_dep (U : Type) (P : U -> Type) (p q : U) (x : P p) (y : P q) :
  existT P p x = existT P q y -> eq_dep _ _ p x q y.
Proof. intros * H; dependent rewrite H; apply eq_dep_intro. Qed.

Section Corollaries.

Variable U : Type.

Definition Inj_dep_pair_on (P : U -> Type) (p : U) (x : P p) :=
  forall (y : P p), existT P p x = existT P p y -> x = y.
Definition Inj_dep_pair := forall P p x, Inj_dep_pair_on P p x.

Lemma eq_dep_eq_on__inj_pair2_on (P : U -> Type) (p : U) (x : P p) :
  Eq_dep_eq_on U P p x -> Inj_dep_pair_on P p x.
Proof. intro ede; red; intros; apply ede; apply eq_sigT_eq_dep; assumption. Qed.
Lemma eq_dep_eq__inj_pair2 : Eq_dep_eq U -> Inj_dep_pair.
Proof (fun eq_dep_eq P p x =>
  @eq_dep_eq_on__inj_pair2_on P p x (eq_dep_eq P p x)).

End Corollaries.

Lemma inj_pair2_eq_dec :
  forall (P : A -> Type) (p : A) (x y : P p), existT P p x = existT P p y -> x = y.
Proof.
  apply eq_dep_eq__inj_pair2.
  apply eq_rect_eq__eq_dep_eq.
  unfold Eq_rect_eq, Eq_rect_eq_on.
  intros; apply eq_rect_eq_dec.
Qed.

End Eq_dec.
