(* -------------------------------------------------------------------- *)
(* Copyright (c) - 2015--2016 - IMDEA Software Institute                *)
(* Copyright (c) - 2015--2018 - Inria                                   *)
(* Copyright (c) - 2016--2018 - Polytechnique                           *)
(* -------------------------------------------------------------------- *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope box_scope.
Declare Scope quant_scope.

(* -------------------------------------------------------------------- *)

Axiom functional_extensionality_dep :
       forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
       (forall x : A, f x = g x) -> f = g.
Axiom propositional_extensionality :
       forall P Q : Prop, P <-> Q -> P = Q.

Axiom constructive_indefinite_description :
  forall (A : Type) (P : A -> Prop),
  (exists x : A, P x) -> {x : A | P x}.
Notation cid := constructive_indefinite_description.

(* -------------------------------------------------------------------- *)
Record mextentionality := {
  _ : forall (P Q : Prop), (P <-> Q) -> (P = Q);
  _ : forall {T U : Type} (f g : T -> U),
        (forall x, f x = g x) -> f = g;
}.

Fact extentionality : mextentionality.
Proof.
split.
- exact: propositional_extensionality.
- by move=> T U f g; apply: functional_extensionality_dep.
Qed.

Lemma propext (P Q : Prop) : (P <-> Q) -> (P = Q).
Proof. by have [propext _] := extentionality; apply: propext. Qed.

Lemma funext {T U : Type} (f g : T -> U) : (f =1 g) -> f = g.
Proof. by case: extentionality=> _; apply. Qed.

Lemma propeqE (P Q : Prop) : (P = Q) = (P <-> Q).
Proof. by apply: propext; split=> [->|/propext]. Qed.


Lemma funeqE {T U : Type} (f g : T -> U) : (f = g) = (f =1 g).
Proof. by rewrite propeqE; split=> [->//|/funext]. Qed.

Lemma funeq2E {T U V : Type} (f g : T -> U -> V) : (f = g) = (f =2 g).
Proof.
by rewrite propeqE; split=> [->//|?]; rewrite funeqE=> x; rewrite funeqE.
Qed.

Lemma funeq3E {T U V W : Type} (f g : T -> U -> V -> W) :
  (f = g) = (forall x y z, f x y z = g x y z).
Proof.
by rewrite propeqE; split=> [->//|?]; rewrite funeq2E=> x y; rewrite funeqE.
Qed.

Lemma predeqE {T} (P Q : T -> Prop) : (P = Q) = (forall x, P x <-> Q x).
Proof.
by rewrite propeqE; split=> [->//|?]; rewrite funeqE=> x; rewrite propeqE.
Qed.

Lemma predeqP {T} (A B : T -> Prop) : (A = B) <-> (forall x, A x <-> B x).
Proof. by rewrite predeqE. Qed.

Lemma predeq2E {T U} (P Q : T -> U -> Prop) :
   (P = Q) = (forall x y, P x y <-> Q x y).
Proof.
by rewrite propeqE; split=> [->//|?]; rewrite funeq2E=> ??; rewrite propeqE.
Qed.

Lemma predeq3E {T U V} (P Q : T -> U -> V -> Prop) :
   (P = Q) = (forall x y z, P x y z <-> Q x y z).
Proof.
by rewrite propeqE; split=> [->//|?]; rewrite funeq3E=> ???; rewrite propeqE.
Qed.

Lemma propT (P : Prop) : P -> P = True.
Proof. by move=> p; rewrite propeqE; tauto. Qed.

Lemma Prop_irrelevance (P : Prop) (x y : P) : x = y.
Proof. by move: x (x) y => /propT-> [] []. Qed.

(* -------------------------------------------------------------------- *)
Record mclassic := {
  _ : forall (P : Prop), {P} + {~P};
  _ : forall T, Choice.mixin_of T
}.

Lemma choice X Y (P : X -> Y -> Prop) :
  (forall x, exists y, P x y) -> {f & forall x, P x (f x)}.
Proof. by move=> /(_ _)/constructive_indefinite_description -/all_tag. Qed.

(* Diaconescu Theorem *)
Theorem EM P : P \/ ~ P.
Proof.
pose U val := fun Q : bool => Q = val \/ P.
have Uex val : exists b, U val b by exists val; left.
pose f val := projT1 (cid (Uex val)).
pose Uf val : U val (f val) := projT2 (cid (Uex val)).
have : f true != f false \/ P.
  have [] := (Uf true, Uf false); rewrite /U.
  by move=> [->|?] [->|?] ; do ?[by right]; left.
move=> [/eqP fTFN|]; [right=> p|by left]; apply: fTFN.
have UTF : U true = U false by rewrite predeqE /U => b; split=> _; right.
rewrite /f; move: (Uex true) (Uex false); rewrite UTF => p1 p2.
by congr (projT1 (cid _)); apply: Prop_irrelevance.
Qed.

Lemma pselect (P : Prop): {P} + {~P}.
Proof.
have : exists b, if b then P else ~ P.
  by case: (EM P); [exists true|exists false].
by move=> /cid [[]]; [left|right].
Qed.

Lemma classic : mclassic.
Proof.
split=> [|T]; first exact: pselect.
exists (fun (P : pred T) (n : nat) =>
  if pselect (exists x, P x) isn't left ex then None
  else Some (projT1 (cid ex)))
  => [P n x|P [x Px]|P Q /funext -> //].
  by case: pselect => // ex [<- ]; case: cid.
by exists 0; case: pselect => // -[]; exists x.
Qed.

Lemma gen_choiceMixin {T : Type} : Choice.mixin_of T.
Proof. by case: classic. Qed.

Lemma pdegen (P : Prop): P = True \/ P = False.
Proof. by have [p|Np] := pselect P; [left|right]; rewrite propeqE. Qed.

Lemma lem (P : Prop): P \/ ~P.
Proof. by case: (pselect P); tauto. Qed.

(* -------------------------------------------------------------------- *)
Lemma trueE : true = True :> Prop.
Proof. by rewrite propeqE; split. Qed.

Lemma falseE : false = False :> Prop.
Proof. by rewrite propeqE; split. Qed.

Lemma propF (P : Prop) : ~ P -> P = False.
Proof. by move=> p; rewrite propeqE; tauto. Qed.

Lemma eq_fun T rT (U V : T -> rT) :
  (forall x : T, U x = V x) -> (fun x => U x) = (fun x => V x).
Proof. by move=> /funext->. Qed.

Lemma eq_fun2 T1 T2 rT (U V : T1 -> T2 -> rT) :
  (forall x y, U x y = V x y) -> (fun x y => U x y) = (fun x y => V x y).
Proof. by move=> UV; rewrite funeq2E => x y; rewrite UV. Qed.

Lemma eq_fun3  T1 T2 T3 rT (U V : T1 -> T2 -> T3 -> rT) :
  (forall x y z, U x y z = V x y z) ->
  (fun x y z => U x y z) = (fun x y z => V x y z).
Proof. by move=> UV; rewrite funeq3E => x y z; rewrite UV. Qed.

Lemma eq_forall T (U V : T -> Prop) :
  (forall x : T, U x = V x) -> (forall x, U x) = (forall x, V x).
Proof. by move=> e; rewrite propeqE; split=> ??; rewrite (e,=^~e). Qed.

Lemma eq_forall2 T S (U V : forall x : T, S x -> Prop) :
  (forall x y, U x y = V x y) -> (forall x y, U x y) = (forall x y, V x y).
Proof. by move=> UV; apply/eq_forall => x; apply/eq_forall. Qed.

Lemma eq_forall3 T S R (U V : forall (x : T) (y : S x), R x y -> Prop) :
  (forall x y z, U x y z = V x y z) ->
  (forall x y z, U x y z) = (forall x y z, V x y z).
Proof. by move=> UV; apply/eq_forall2 => x y; apply/eq_forall. Qed.

Lemma eq_exists T (U V : T -> Prop) :
  (forall x : T, U x = V x) -> (exists x, U x) = (exists x, V x).
Proof.
by move=> e; rewrite propeqE; split=> - [] x ?; exists x; rewrite (e,=^~e).
Qed.

Lemma eq_exists2 T S (U V : forall x : T, S x -> Prop) :
  (forall x y, U x y = V x y) -> (exists x y, U x y) = (exists x y, V x y).
Proof. by move=> UV; apply/eq_exists => x; apply/eq_exists. Qed.

Lemma eq_exists3 T S R (U V : forall (x : T) (y : S x), R x y -> Prop) :
  (forall x y z, U x y z = V x y z) ->
  (exists x y z, U x y z) = (exists x y z, V x y z).
Proof. by move=> UV; apply/eq_exists2 => x y; apply/eq_exists. Qed.

Lemma eq_exist T (P : T -> Prop) (s t : T) (p : P s) (q : P t) :
  s = t -> exist P s p = exist P t q.
Proof. by move=> st; case: _ / st in q *; apply/congr1/Prop_irrelevance. Qed.

Lemma forall_swap T S (U : forall (x : T) (y : S), Prop) :
   (forall x y, U x y) = (forall y x, U x y).
Proof. by rewrite propeqE; split. Qed.

Lemma exists_swap T S (U : forall (x : T) (y : S), Prop) :
   (exists x y, U x y) = (exists y x, U x y).
Proof. by rewrite propeqE; split => -[x [y]]; exists y, x. Qed.

Lemma reflect_eq (P : Prop) (b : bool) : reflect P b -> P = b.
Proof. by rewrite propeqE; exact: rwP. Qed.

Definition asbool (P : Prop) :=
  if pselect P then true else false.

Notation "`[< P >]" := (asbool P) : bool_scope.

Lemma asboolE (P : Prop) : `[<P>] = P :> Prop.
Proof. by rewrite propeqE /asbool; case: pselect; split. Qed.

Lemma asboolP (P : Prop) : reflect P `[<P>].
Proof. by apply: (equivP idP); rewrite asboolE. Qed.

Lemma asboolb (b : bool) : `[< b >] = b.
Proof. by apply/asboolP/idP. Qed.

Lemma asboolPn (P : Prop) : reflect (~ P) (~~ `[<P>]).
Proof. by rewrite /asbool; case: pselect=> h; constructor. Qed.

Lemma asboolW (P : Prop) : `[<P>] -> P.
Proof. by case: asboolP. Qed.

(* Shall this be a coercion ?*)
Lemma asboolT (P : Prop) : P -> `[<P>].
Proof. by case: asboolP. Qed.

Lemma asboolF (P : Prop) : ~ P -> `[<P>] = false.
Proof. by apply/introF/asboolP. Qed.

Definition equality_mixin_of_Type (T : Type) : Equality.mixin_of T :=
  EqMixin (fun x y : T => asboolP (x = y)).

Definition choice_of_Type (T : Type) : choiceType :=
  Choice.Pack (Choice.Class (equality_mixin_of_Type T) gen_choiceMixin).

Lemma is_true_inj : injective is_true.
Proof. by move=> [] []; rewrite ?(trueE, falseE) ?propeqE; tauto. Qed.

Lemma not_True : (~ True) = False. Proof. exact/propext. Qed.
Lemma not_False : (~ False) = True. Proof. by apply/propext; split=> _. Qed.

(* -------------------------------------------------------------------- *)
Lemma asbool_equiv_eq {P Q : Prop} : (P <-> Q) -> `[<P>] = `[<Q>].
Proof. by rewrite -propeqE => ->. Qed.

Lemma asbool_equiv_eqP {P Q : Prop} b : reflect Q b -> (P <-> Q) -> `[<P>] = b.
Proof. by move=> Q_b [PQ QP]; apply/asboolP/Q_b. Qed.

Lemma asbool_equiv {P Q : Prop} : (P <-> Q) -> (`[<P>] <-> `[<Q>]).
Proof. by move/asbool_equiv_eq->. Qed.

Lemma asbool_eq_equiv {P Q : Prop} : `[<P>] = `[<Q>] -> (P <-> Q).
Proof. by move=> eq; split=> /asboolP; rewrite (eq, =^~ eq) => /asboolP. Qed.

(* -------------------------------------------------------------------- *)
Lemma and_asboolP (P Q : Prop) : reflect (P /\ Q) (`[< P >] && `[< Q >]).
Proof.
apply: (iffP idP); first by case/andP => /asboolP p /asboolP q.
by case=> /asboolP-> /asboolP->.
Qed.

Lemma and3_asboolP (P Q R : Prop) :
  reflect [/\ P, Q & R] [&& `[< P >], `[< Q >] & `[< R >]].
Proof.
apply: (iffP idP); first by case/and3P => /asboolP p /asboolP q /asboolP r.
by case => /asboolP -> /asboolP -> /asboolP ->.
Qed.

Lemma or_asboolP (P Q : Prop) : reflect (P \/ Q) (`[< P >] || `[< Q >]).
Proof.
apply: (iffP idP); first by case/orP=> /asboolP; [left | right].
by case=> /asboolP-> //=; rewrite orbT.
Qed.

Lemma or3_asboolP (P Q R : Prop) :
  reflect [\/ P, Q | R] [|| `[< P >], `[< Q >] | `[< R >]].
Proof.
apply: (iffP idP); last by case=> [| |] /asboolP -> //=; rewrite !orbT.
by case/orP=> [/asboolP p|/orP[]/asboolP]; [exact:Or31|exact:Or32|exact:Or33].
Qed.

Lemma asbool_neg {P : Prop} : `[<~ P>] = ~~ `[<P>].
Proof. by apply/idP/asboolPn=> [/asboolP|/asboolT]. Qed.

Lemma asbool_or {P Q : Prop} : `[<P \/ Q>] = `[<P>] || `[<Q>].
Proof. exact: (asbool_equiv_eqP (or_asboolP _ _)). Qed.

Lemma asbool_and {P Q : Prop} : `[<P /\ Q>] = `[<P>] && `[<Q>].
Proof. exact: (asbool_equiv_eqP (and_asboolP _ _)). Qed.

(* -------------------------------------------------------------------- *)
Lemma imply_asboolP {P Q : Prop} : reflect (P -> Q) (`[<P>] ==> `[<Q>]).
Proof.
apply: (iffP implyP)=> [PQb /asboolP/PQb/asboolW //|].
by move=> PQ /asboolP/PQ/asboolT.
Qed.

Lemma asbool_imply {P Q : Prop} : `[<P -> Q>] = `[<P>] ==> `[<Q>].
Proof. exact: (asbool_equiv_eqP imply_asboolP). Qed.

Lemma imply_asboolPn (P Q : Prop) : reflect (P /\ ~ Q) (~~ `[<P -> Q>]).
Proof.
apply: (iffP idP).
by rewrite asbool_imply negb_imply -asbool_neg => /and_asboolP.
by move/and_asboolP; rewrite asbool_neg -negb_imply asbool_imply.
Qed.

(* -------------------------------------------------------------------- *)
Lemma forall_asboolP {T : Type} (P : T -> Prop) :
  reflect (forall x, `[<P x>]) (`[<forall x, P x>]).
Proof.
apply: (iffP idP); first by move/asboolP=> Px x; apply/asboolP.
by move=> Px; apply/asboolP=> x; apply/asboolP.
Qed.

Lemma exists_asboolP {T : Type} (P : T -> Prop) :
  reflect (exists x, `[<P x>]) (`[<exists x, P x>]).
Proof.
apply: (iffP idP); first by case/asboolP=> x Px; exists x; apply/asboolP.
by case=> x bPx; apply/asboolP; exists x; apply/asboolP.
Qed.

(* -------------------------------------------------------------------- *)

Lemma contra_notP (Q P : Prop) : (~ Q -> P) -> ~ P -> Q.
Proof.
move=> cb /asboolPn nb; apply/asboolP.
by apply: contraR nb => /asboolP /cb /asboolP.
Qed.

Lemma contraPP (Q P : Prop) : (~ Q -> ~ P) -> P -> Q.
Proof.
move=> cb /asboolP hb; apply/asboolP.
by apply: contraLR hb => /asboolP /cb /asboolPn.
Qed.

Lemma contrapT P : ~ ~ P -> P.
Proof.
by move/asboolPn=> nnb; apply/asboolP; apply: contraR nnb => /asboolPn /asboolP.
Qed.

Lemma wlog_neg P : (~ P -> P) -> P.
Proof. by move=> ?; case: (pselect P). Qed.

Lemma notT (P : Prop) : P = False -> ~ P. Proof. by move->. Qed.

Lemma notTE (P : Prop) : (~ P) -> P = False. Proof. by case: (pdegen P)=> ->. Qed.
Lemma notFE (P : Prop) : (~ P) = False -> P.
Proof. move/notT; exact: contrapT. Qed.

Lemma notK : involutive not.
Proof.
move=> P; case: (pdegen P)=> ->; last by apply: notTE; intuition.
by rewrite [~ True]notTE //; case: (pdegen (~ False)) => // /notFE.
Qed.

Lemma not_inj : injective not. Proof. exact: can_inj notK. Qed.
Lemma notLR P Q : (P = ~ Q) -> (~ P) = Q. Proof. exact: canLR notK. Qed.

Lemma notRL P Q : (~ P) = Q -> P = ~ Q. Proof. exact: canRL notK. Qed.

Lemma iff_notr (P Q : Prop) : (P <-> ~ Q) <-> (~ P <-> Q).
Proof. by split=> [/propext ->|/propext <-]; rewrite notK. Qed.

Lemma iff_not2 (P Q : Prop) : (~ P <-> ~ Q) <-> (P <-> Q).
Proof. by split=> [/iff_notr|PQ]; [|apply/iff_notr]; rewrite notK. Qed.

(* -------------------------------------------------------------------- *)
(* assia : let's see if we need the simplpred machinery. In any case, we sould
   first try definitions + appropriate Arguments setting to see whether these
   can replace the canonical structures machinery. *)

Definition predp T := T -> Prop.

Identity Coercion fun_of_pred : predp >-> Funclass.

Definition relp T := T -> predp T.

Identity Coercion fun_of_rel : rel >-> Funclass.

Notation xpredp0 := (fun _ => False).
Notation xpredpT := (fun _ => True).
Notation xpredpI := (fun (p1 p2 : predp _) x => p1 x /\ p2 x).
Notation xpredpU := (fun (p1 p2 : predp _) x => p1 x \/ p2 x).
Notation xpredpC := (fun (p : predp _) x => ~ p x).
Notation xpredpD := (fun (p1 p2 : predp _) x => ~ p2 x /\ p1 x).
Notation xpreimp := (fun f (p : predp _) x => p (f x)).
Notation xrelpU := (fun (r1 r2 : relp _) x y => r1 x y \/ r2 x y).

(* -------------------------------------------------------------------- *)
Definition pred0p (T : Type) (P : predp T) : bool := `[<P =1 xpredp0>].
Prenex Implicits pred0p.

Lemma pred0pP  (T : Type) (P : predp T) : reflect (P =1 xpredp0) (pred0p P).
Proof. by apply: (iffP (asboolP _)). Qed.

(* -------------------------------------------------------------------- *)
Module BoolQuant.

Inductive box := Box of bool.

Bind    Scope box_scope with box.
Delimit Scope box_scope with P.

Definition idbox {T : Type} (B : box) := fun (x : T) => B.

Definition unbox {T : Type} (B : T -> box) : bool :=
  asbool (forall x : T, let: Box b := B x in b).

Notation "F ^*" := (Box F) (at level 2).
Notation "F ^~" := (~~ F) (at level 2).

Section Definitions.

Variable T : Type.
Implicit Types (B : box) (x y : T).

Definition quant0p Bp := pred0p (fun x : T => let: F^* := Bp x x in F).
(* The first redundant argument protects the notation from  Coq's K-term      *)
(* display kludge; the second protects it from simpl and /=.                  *)
Definition ex B x y := B.
(* Binding the predicate value rather than projecting it prevents spurious    *)
(* unfolding of the boolean connectives by unification.                       *)
Definition all B x y := let: F^* := B in F^~^*.
Definition all_in C B x y := let: F^* := B in (C ==> F)^~^*.
Definition ex_in C B x y :=  let: F^* := B in (C && F)^*.

End Definitions.

Notation "`[ x | B ]" := (quant0p (fun x => B x)) (at level 0, x ident).
Notation "`[ x : T | B ]" := (quant0p (fun x : T => B x)) (at level 0, x ident).

Module Exports.

Delimit Scope quant_scope with Q. (* Bogus, only used to declare scope. *)
Bind Scope quant_scope with box.

Notation ", F" := F^* (at level 200, format ", '/ '  F") : quant_scope.

Notation "`[ 'forall' x B ]" := `[x | all B]
  (at level 0, x at level 99, B at level 200,
   format "`[ '[hv' 'forall'  x B ] ']'") : bool_scope.

Notation "`[ 'forall' x : T B ]" := `[x : T | all B]
  (at level 0, x at level 99, B at level 200, only parsing) : bool_scope.
Notation "`[ 'forall' ( x | C ) B ]" := `[x | all_in C B]
  (at level 0, x at level 99, B at level 200,
   format "`[ '[hv' '[' 'forall'  ( x '/  '  |  C ) ']' B ] ']'") : bool_scope.
Notation "`[ 'forall' ( x : T | C ) B ]" := `[x : T | all_in C B]
  (at level 0, x at level 99, B at level 200, only parsing) : bool_scope.
Notation "`[ 'forall' x 'in' A B ]" := `[x | all_in (x \in A) B]
  (at level 0, x at level 99, B at level 200,
   format "`[ '[hv' '[' 'forall'  x '/  '  'in'  A ']' B ] ']'") : bool_scope.
Notation "`[ 'forall' x : T 'in' A B ]" := `[x : T | all_in (x \in A) B]
  (at level 0, x at level 99, B at level 200, only parsing) : bool_scope.
Notation ", 'forall' x B" := `[x | all B]^*
  (at level 200, x at level 99, B at level 200,
   format ", '/ '  'forall'  x B") : quant_scope.
Notation ", 'forall' x : T B" := `[x : T | all B]^*
  (at level 200, x at level 99, B at level 200, only parsing) : quant_scope.
Notation ", 'forall' ( x | C ) B" := `[x | all_in C B]^*
  (at level 200, x at level 99, B at level 200,
   format ", '/ '  '[' 'forall'  ( x '/  '  |  C ) ']' B") : quant_scope.
Notation ", 'forall' ( x : T | C ) B" := `[x : T | all_in C B]^*
  (at level 200, x at level 99, B at level 200, only parsing) : quant_scope.
Notation ", 'forall' x 'in' A B" := `[x | all_in (x \in A) B]^*
  (at level 200, x at level 99, B at level 200,
   format ", '/ '  '[' 'forall'  x '/  '  'in'  A ']' B") : bool_scope.
Notation ", 'forall' x : T 'in' A B" := `[x : T | all_in (x \in A) B]^*
  (at level 200, x at level 99, B at level 200, only parsing) : bool_scope.

Notation "`[ 'exists' x B ]" := `[x | ex B]^~
  (at level 0, x at level 99, B at level 200,
   format "`[ '[hv' 'exists'  x B ] ']'") : bool_scope.
Notation "`[ 'exists' x : T B ]" := `[x : T | ex B]^~
  (at level 0, x at level 99, B at level 200, only parsing) : bool_scope.
Notation "`[ 'exists' ( x | C ) B ]" := `[x | ex_in C B]^~
  (at level 0, x at level 99, B at level 200,
   format "`[ '[hv' '[' 'exists'  ( x '/  '  |  C ) ']' B ] ']'") : bool_scope.
Notation "`[ 'exists' ( x : T | C ) B ]" := `[x : T | ex_in C B]^~
  (at level 0, x at level 99, B at level 200, only parsing) : bool_scope.
Notation "`[ 'exists' x 'in' A B ]" := `[x | ex_in (x \in A) B]^~
  (at level 0, x at level 99, B at level 200,
   format "`[ '[hv' '[' 'exists'  x '/  '  'in'  A ']' B ] ']'") : bool_scope.
Notation "`[ 'exists' x : T 'in' A B ]" := `[x : T | ex_in (x \in A) B]^~
  (at level 0, x at level 99, B at level 200, only parsing) : bool_scope.
Notation ", 'exists' x B" := `[x | ex B]^~^*
  (at level 200, x at level 99, B at level 200,
   format ", '/ '  'exists'  x B") : quant_scope.
Notation ", 'exists' x : T B" := `[x : T | ex B]^~^*
  (at level 200, x at level 99, B at level 200, only parsing) : quant_scope.
Notation ", 'exists' ( x | C ) B" := `[x | ex_in C B]^~^*
  (at level 200, x at level 99, B at level 200,
   format ", '/ '  '[' 'exists'  ( x '/  '  |  C ) ']' B") : quant_scope.
Notation ", 'exists' ( x : T | C ) B" := `[x : T | ex_in C B]^~^*
  (at level 200, x at level 99, B at level 200, only parsing) : quant_scope.
Notation ", 'exists' x 'in' A B" := `[x | ex_in (x \in A) B]^~^*
  (at level 200, x at level 99, B at level 200,
   format ", '/ '  '[' 'exists'  x '/  '  'in'  A ']' B") : bool_scope.
Notation ", 'exists' x : T 'in' A B" := `[x : T | ex_in (x \in A) B]^~^*
  (at level 200, x at level 99, B at level 200, only parsing) : bool_scope.

End Exports.

End BoolQuant.
Export BoolQuant.Exports.

Local Open Scope quant_scope.

(* -------------------------------------------------------------------- *)
Section QuantifierCombinators.

Variables (T : Type) (P : pred T) (PP : predp T).
Hypothesis viewP : forall x, reflect (PP x) (P x).

Lemma existsPP : reflect (exists x, PP x) `[exists x, P x].
Proof.
apply: (iffP idP).
  move/asboolP; (* oops notation! *) apply: contra_notP => nh x /=; apply: notTE.
  by apply: contra_not nh => /viewP Px; exists x.
case=> x PPx; apply/asboolP=> /(_ x) /notT /=; rewrite -/(not (~ P x)) notK.
exact/viewP.
Qed.

Lemma forallPP : reflect (forall x, PP x) `[forall x, P x].
Proof.
apply: (iffP idP).
  by move/asboolP=> h x; move/notT: (h x)=> /= /negP; rewrite negbK => /viewP.
move=> h; apply/asboolP=> x; apply/notTE/negP; rewrite negbK; exact/viewP.
Qed.

End QuantifierCombinators.

Section PredQuantifierCombinators.

Variables (T : Type) (P : pred T).

Lemma existsbP : reflect (exists x, P x) `[exists x, P x].
Proof. exact: existsPP (fun x => @idP (P x)). Qed.

Lemma existsbE : `[exists x, P x] = `[<exists x, P x>].
Proof.
apply/esym/is_true_inj; rewrite asboolE propeqE; apply: rwP; exact: existsbP.
Qed.

Lemma forallbP : reflect (forall x, P x) `[forall x, P x].
Proof. exact: forallPP (fun x => @idP (P x)). Qed.

Lemma forallbE : `[forall x, P x] = `[<forall x, P x>].
Proof.
apply/esym/is_true_inj; rewrite asboolE propeqE; apply: rwP; exact: forallbP.
Qed.

End PredQuantifierCombinators.

(* -------------------------------------------------------------------- *)
Lemma existsp_asboolP {T} {P : T -> Prop} :
  reflect (exists x : T, P x) `[exists x : T, `[<P x>]].
Proof. exact: existsPP (fun x => @asboolP (P x)). Qed.

Lemma forallp_asboolP {T} {P : T -> Prop} :
  reflect (forall x : T, P x) `[forall x : T, `[<P x>]].
Proof. exact: forallPP (fun x => @asboolP (P x)). Qed.

Lemma forallp_asboolPn {T} {P : T -> Prop} :
  reflect (forall x : T, ~ P x) (~~ `[<exists x : T, P x>]).
Proof.
apply: (iffP idP)=> [/asboolPn NP x Px|NP].
by apply/NP; exists x. by apply/asboolP=> -[x]; apply/NP.
Qed.

Lemma existsp_asboolPn {T} {P : T -> Prop} :
  reflect (exists x : T, ~ P x) (~~ `[<forall x : T, P x>]).
Proof.
apply: (iffP idP); last by case=> x NPx; apply/asboolPn=> /(_ x).
move/asboolPn=> NP; apply/asboolP/negbNE/asboolPn=> h.
by apply/NP=> x; apply/asboolP/negbNE/asboolPn=> NPx; apply/h; exists x.
Qed.

Lemma asbool_forallNb {T : Type} (P : pred T) :
  `[< forall x : T, ~~ (P x) >] = ~~ `[< exists x : T, P x >].
Proof.
apply: (asbool_equiv_eqP forallp_asboolPn);
  by split=> h x; apply/negP/h.
Qed.

Lemma asbool_existsNb {T : Type} (P : pred T) :
  `[< exists x : T, ~~ (P x) >] = ~~ `[< forall x : T, P x >].
Proof.
apply: (asbool_equiv_eqP existsp_asboolPn);
  by split=> -[x h]; exists x; apply/negP.
Qed.

Lemma not_implyP (P Q : Prop) : ~ (P -> Q) <-> P /\ ~ Q.
Proof.
split=> [/asboolP|[p nq pq]]; [|exact/nq/pq].
by rewrite asbool_neg => /imply_asboolPn.
Qed.

Lemma not_andP (P Q : Prop) : ~ (P /\ Q) <-> ~ P \/ ~ Q.
Proof.
split => [/asboolPn|[|]]; try by apply: contra_not => -[].
by rewrite asbool_and negb_and => /orP[]/asboolPn; [left|right].
Qed.

Lemma not_and3P (P Q R : Prop) : ~ [/\ P, Q & R] <-> [\/ ~ P, ~ Q | ~ R].
Proof.
split=> [/and3_asboolP|/or3_asboolP].
by rewrite 2!negb_and -3!asbool_neg => /or3_asboolP.
by rewrite 3!asbool_neg -2!negb_and => /and3_asboolP.
Qed.

Lemma not_orP (P Q : Prop) : ~ (P \/ Q) <-> ~ P /\ ~ Q.
Proof.
split; [apply: contra_notP => /not_andP|apply: contraPnot => AB; apply/not_andP];
  by rewrite 2!notK.
Qed.

Lemma not_implyE (P Q : Prop) : (~ (P -> Q)) = (P /\ ~ Q).
Proof. by rewrite propeqE not_implyP. Qed.

Lemma orC (P Q : Prop) : (P \/ Q) = (Q \/ P).
Proof. by rewrite propeqE; split=> [[]|[]]; [right|left|right|left]. Qed.

Lemma orA : associative or.
Proof. by move=> P Q R; rewrite propeqE; split=> [|]; tauto. Qed.

Lemma andC (P Q : Prop) : (P /\ Q) = (Q /\ P).
Proof. by rewrite propeqE; split=> [[]|[]]. Qed.

Lemma andA : associative and.
Proof. by move=> P Q R; rewrite propeqE; split=> [|]; tauto. Qed.

Lemma forallNE {T} (P : T -> Prop) : (forall x, ~ P x) = ~ exists x, P x.
Proof.
by rewrite propeqE; split => [fP [x /fP]//|nexP x Px]; apply: nexP; exists x.
Qed.

Lemma existsNE {T} (P : T -> Prop) : (exists x, ~ P x) = ~ forall x, P x.
Proof.
rewrite propeqE; split=> [[x Px] aP //|NaP].
by apply: contrapT; rewrite -forallNE => aP; apply: NaP => x; apply: contrapT.
Qed.

Lemma existsNP T (P : T -> Prop) : (exists x, ~ P x) <-> ~ forall x, P x.
Proof. by rewrite existsNE. Qed.

Lemma not_existsP T (P : T -> Prop) : (exists x, P x) <-> ~ forall x, ~ P x.
Proof. by rewrite forallNE notK. Qed.

Lemma forallNP T (P : T -> Prop) : (forall x, ~ P x) <-> ~ exists x, P x.
Proof. by rewrite forallNE. Qed.

Lemma not_forallP T (P : T -> Prop) : (forall x, P x) <-> ~ exists x, ~ P x.
Proof. by rewrite existsNE notK. Qed.

Lemma not_exists2P T (P Q : T -> Prop) :
  (exists2 x, P x & Q x) <-> ~ forall x, ~ P x \/ ~ Q x.
Proof.
split=> [[x Px Qx] /(_ x) [|]//|]; apply: contra_notP => PQ t.
by rewrite -not_andP; apply: contra_not PQ => -[Pt Qt]; exists t.
Qed.

Lemma forall2NP T (P Q : T -> Prop) :
  (forall x, ~ P x \/ ~ Q x) <-> ~ (exists2 x, P x & Q x).
Proof.
split=> [PQ [t Pt Qt]|PQ t]; first by have [] := PQ t.
by rewrite -not_andP => -[Pt Qt]; apply PQ; exists t.
Qed.

Lemma exists2P T (P Q : T -> Prop) :
  (exists2 x, P x & Q x) <-> exists x, P x /\ Q x.
Proof. by split=> [[x ? ?] | [x []]]; exists x. Qed.

(* -------------------------------------------------------------------- *)
Definition xchooseb {T : choiceType} (P : pred T) (h : `[exists x, P x]) :=
  xchoose (existsbP P h).

Lemma xchoosebP {T : choiceType} (P : pred T) (h : `[exists x, P x]) :
  P (xchooseb h).
Proof. exact/xchooseP. Qed.

(* -------------------------------------------------------------------- *)
(* FIXME: to be moved                                                   *)
Lemma imsetbP (T : Type) (U : eqType) (f : T -> U) v :
  reflect (exists x, v = f x) (v \in [pred y | `[exists x, y == f x]]).
Proof. by apply: (iffP (existsbP _))=> -[x] => [/eqP|] ->; exists x. Qed.
