(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrfun ssrbool eqtype choice.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Record mclassic := {
  _ : forall (P : Prop), {P}+{~P};
  _ : forall (P : Prop), P = True \/ P = False
}.

Axiom classic : mclassic.

(* -------------------------------------------------------------------- *)
Lemma pselect (P : Prop): {P}+{~P}.
Proof. by case classic. Qed.

Lemma pdegen (P : Prop): P = True \/ P = False.
Proof. by case classic. Qed.

Lemma lem (P : Prop): P \/ ~P.
Proof. by case: (pselect P); tauto. Qed.

(* -------------------------------------------------------------------- *)
Definition asbool (P : Prop) :=
  if pselect P then true else false.

Notation "`[ P ]" := (asbool P) : bool_scope.

Lemma asboolP (P : Prop) : reflect P `[P].
Proof. by rewrite /asbool; case: pselect=> h; constructor. Qed.

Lemma asboolPn (P : Prop) : reflect (~ P) (~~ `[P]).
Proof. by rewrite /asbool; case: pselect=> h; constructor. Qed.

Lemma asboolE (P : Prop) : `[P] -> P.
Proof. by case: asboolP. Qed.

(* Shall this be a coercion ?*)
Lemma asboolT (P : Prop) : P -> `[P].
Proof. by case: asboolP. Qed.

Lemma and_asboolP (P Q : Prop) : reflect (P /\ Q) (`[P] && `[Q]).
Proof.
apply: (iffP idP); first by case/andP=> /asboolP hP /asboolP hQ.
by case=> /asboolP-> /asboolP->.
Qed.

Lemma or_asboolP (P Q : Prop) : reflect (P \/ Q) (`[P] || `[Q]).
Proof.
apply: (iffP idP); first by case/orP=> /asboolP; [left | right].
by case=> /asboolP-> //=; rewrite orbT.
Qed.

Lemma forall_asboolP {T : Type} (P : T -> Prop) :
  reflect (forall x, `[P x]) (`[forall x, P x]).
Proof.
apply: (iffP idP); first by move/asboolP=> Px x; apply/asboolP.
by move=> Px; apply/asboolP=> x; apply/asboolP.
Qed.

Lemma exists_asboolP {T : Type} (P : T -> Prop) :
  reflect (exists x, `[P x]) (`[exists x, P x]).
Proof.
apply: (iffP idP); first by case/asboolP=> x Px; exists x; apply/asboolP.
by case=> x bPx; apply/asboolP; exists x; apply/asboolP.
Qed.

Lemma asbool_equiv_eq {P Q : Prop} : (P <-> Q) -> `[P] = `[Q].
Proof.
case: (pselect P) => [hP | hnP] PQ.
  by move/asboolP: (hP)->; move/PQ/asboolP: (hP)->.
by move/asboolPn/negbTE: (hnP) => ->; move/PQ/asboolPn/negbTE: hnP->.
Qed.

Lemma asbool_equiv {P Q : Prop} : (P <-> Q) -> (`[P] <-> `[Q]).
Proof. by move/asbool_equiv_eq->. Qed.


(* -------------------------------------------------------------------- *)

Lemma contrap (Q P : Prop) : (Q -> P) -> ~ P -> ~ Q.
Proof.
move=> cb /asboolPn nb; apply/asboolPn.
by apply: contra nb => /asboolP /cb /asboolP.
Qed.

Definition contrapNN := contra.

Lemma contrapL (Q P : Prop) : (Q -> ~ P) -> P -> ~ Q.
Proof.
move=> cb /asboolP hb; apply/asboolPn.
by apply: contraL hb => /asboolP /cb /asboolPn.
Qed.

Definition contrapTN := contrapL.

Lemma contrapR (Q P : Prop) : (~ Q -> P) -> ~ P -> Q.
Proof.
move=> cb /asboolPn nb; apply/asboolP.
by apply: contraR nb => /asboolP /cb /asboolP.
Qed.

Definition contrapNT := contrapR.

Lemma contrapLR (Q P : Prop) : (~ Q -> ~ P) -> P -> Q.
Proof.
move=> cb /asboolP hb; apply/asboolP.
by apply: contraLR hb => /asboolP /cb /asboolPn.
Qed.

Definition contrapTT := contrapLR.

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
Definition pred0p (T : Type) (P : predp T) : bool := `[P =1 xpredp0].
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

Open Scope quant_scope.



Section QuantifierCombinators.

Variables (T : Type) (P : pred T) (PP : predp T).
Hypothesis viewP : forall x, reflect (PP x) (P x).

Lemma existsPP : reflect (exists x, PP x) `[exists x, P x].
Proof.
apply: (iffP idP).
  move/asboolP; (* oops notation! *) apply: contrapR => nh x /=; apply: notTE.
  by apply: contrap nh => /viewP Px; exists x.
case=> x PPx; apply/asboolP=> /(_ x) [] /notT /=; rewrite -/(not (~ P x)) notK.
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

Lemma forallbP : reflect (forall x, P x) `[forall x, P x].
Proof. exact: forallPP (fun x => @idP (P x)). Qed.

End PredQuantifierCombinators.

Definition xchooseb {T : choiceType} (P : pred T) (h : `[exists x, P x]) :=
  xchoose (existsbP P h).

Lemma xchoosebP {T : choiceType} (P : pred T) (h : `[exists x, P x]) :
  P (xchooseb h).
Proof. exact/xchooseP. Qed.

(* Notation "'exists_ view" := (existsPP (fun _ => view)) *)
(*   (at level 4, right associativity, format "''exists_' view"). *)
(* Notation "'forall_ view" := (forallPP (fun _ => view)) *)
(*   (at level 4, right associativity, format "''forall_' view"). *)


(* Section Quantifiers. *)

(* Variables (T : Type) (rT : T -> eqType). *)
(* Implicit Type (D P : rset T) (f : forall x, rT x). *)

(* Lemma forallP P : reflect (forall x, P x) [forall x, P x]. *)
(* Proof. *)
(* About forallPP. *)
(* have:= (forallPP (fun x => (asboolP (P x)))). *)
(* exact: 'forall_asboolP. Qed. *)

(* Lemma eqfunP f1 f2 : reflect (forall x, f1 x = f2 x) [forall x, f1 x == f2 x]. *)
(* Proof. exact: 'forall_eqP. Qed. *)

(* Lemma forall_inP D P : reflect (forall x, D x -> P x) [forall (x | D x), P x]. *)
(* Proof. exact: 'forall_implyP. Qed. *)

(* Lemma eqfun_inP D f1 f2 : *)
(*   reflect {in D, forall x, f1 x = f2 x} [forall (x | x \in D), f1 x == f2 x]. *)
(* Proof. by apply: (iffP 'forall_implyP) => eq_f12 x Dx; apply/eqP/eq_f12. Qed. *)

(* Lemma existsP P : reflect (exists x, P x) [exists x, P x]. *)
(* Proof. exact: 'exists_idP. Qed. *)

(* Lemma exists_eqP f1 f2 : *)
(*   reflect (exists x, f1 x = f2 x) [exists x, f1 x == f2 x]. *)

(* Proof. exact: 'exists_eqP. Qed. *)

(* Lemma exists_inP D P : reflect (exists2 x, D x & P x) [exists (x | D x), P x]. *)
(* Proof. by apply: (iffP 'exists_andP) => [[x []] | [x]]; exists x. Qed. *)

(* Lemma exists_eq_inP D f1 f2 : *)
(*   reflect (exists2 x, D x & f1 x = f2 x) [exists (x | D x), f1 x == f2 x]. *)
(* Proof. by apply: (iffP (exists_inP _ _)) => [] [x Dx /eqP]; exists x. Qed. *)

(* Lemma eq_existsb P1 P2 : P1 =1 P2 -> [exists x, P1 x] = [exists x, P2 x]. *)
(* Proof. by move=> eqP12; congr (_ != 0); apply: eq_card. Qed. *)

(* Lemma eq_existsb_in D P1 P2 : *)
(*     (forall x, D x -> P1 x = P2 x) -> *)
(*   [exists (x | D x), P1 x] = [exists (x | D x), P2 x]. *)
(* Proof. by move=> eqP12; apply: eq_existsb => x; apply: andb_id2l => /eqP12. Qed. *)

(* Lemma eq_forallb P1 P2 : P1 =1 P2 -> [forall x, P1 x] = [forall x, P2 x]. *)
(* Proof. by move=> eqP12; apply/negb_inj/eq_existsb=> /= x; rewrite eqP12. Qed. *)

(* Lemma eq_forallb_in D P1 P2 : *)
(*     (forall x, D x -> P1 x = P2 x) -> *)
(*   [forall (x | D x), P1 x] = [forall (x | D x), P2 x]. *)
(* Proof. *)
(* by move=> eqP12; apply: eq_forallb => i; case Di: (D i); rewrite // eqP12. *)
(* Qed. *)

(* Lemma negb_forall P : ~~ [forall x, P x] = [exists x, ~~ P x]. *)
(* Proof. by []. Qed. *)

(* Lemma negb_forall_in D P : *)
(*   ~~ [forall (x | D x), P x] = [exists (x | D x), ~~ P x]. *)
(* Proof. by apply: eq_existsb => x; rewrite negb_imply. Qed. *)

(* Lemma negb_exists P : ~~ [exists x, P x] = [forall x, ~~ P x]. *)
(* Proof. by apply/negbLR/esym/eq_existsb=> x; apply: negbK. Qed. *)

(* Lemma negb_exists_in D P : *)
(*   ~~ [exists (x | D x), P x] = [forall (x | D x), ~~ P x]. *)
(* Proof. by rewrite negb_exists; apply/eq_forallb => x; rewrite [~~ _]fun_if. Qed. *)

(* End Quantifiers. *)
