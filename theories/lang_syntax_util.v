Require Import String.
From HB Require Import structures.
Require Import Classical_Prop. (* NB: to compile with Coq 8.17 *)
From mathcomp Require Import all_ssreflect.
Require Import signed.

(******************************************************************************)
(*                  Shared by lang_syntax_*.v files                           *)
(******************************************************************************)

HB.instance Definition _ := hasDecEq.Build string eqb_spec.

Ltac inj_ex H := revert H;
  match goal with
  | |- existT ?P ?l (existT ?Q ?t (existT ?R ?u (existT ?T ?v ?v1))) =
       existT ?P ?l (existT ?Q ?t (existT ?R ?u (existT ?T ?v ?v2))) -> _ =>
    (intro H; do 4 apply Classical_Prop.EqdepTheory.inj_pair2 in H)
  | |- existT ?P ?l (existT ?Q ?t (existT ?R ?u ?v1)) =
       existT ?P ?l (existT ?Q ?t (existT ?R ?u ?v2)) -> _ =>
    (intro H; do 3 apply Classical_Prop.EqdepTheory.inj_pair2 in H)
  | |- existT ?P ?l (existT ?Q ?t ?v1) =
       existT ?P ?l (existT ?Q ?t ?v2) -> _ =>
    (intro H; do 2 apply Classical_Prop.EqdepTheory.inj_pair2 in H)
  | |- existT ?P ?l (existT ?Q ?t ?v1) =
       existT ?P ?l (existT ?Q ?t' ?v2) -> _ =>
    (intro H; do 2 apply Classical_Prop.EqdepTheory.inj_pair2 in H)
  | |- existT ?P ?l ?v1 =
       existT ?P ?l ?v2 -> _ =>
    (intro H; apply Classical_Prop.EqdepTheory.inj_pair2 in H)
  | |- existT ?P ?l ?v1 =
       existT ?P ?l' ?v2 -> _ =>
    (intro H; apply Classical_Prop.EqdepTheory.inj_pair2 in H)
end.

Set Implicit Arguments.
Unset Strict Implicit.
Set Printing Implicit Defensive.

Section tagged_context.
Context {T : eqType} {t0 : T}.
Let ctx := seq (string * T).
Implicit Types (str : string) (g : ctx) (t : T).

Definition dom g := map fst g.

Definition lookup g str := nth t0 (map snd g) (index str (dom g)).

Structure tagged_ctx := Tag {untag : ctx}.

Structure find str t := Find {
  ctx_of : tagged_ctx ;
  #[canonical=no] ctx_prf : t = lookup (untag ctx_of) str}.

Lemma ctx_prf_head str t g : t = lookup ((str, t) :: g) str.
Proof. by rewrite /lookup /= !eqxx. Qed.

Lemma ctx_prf_tail str t g str' t' :
  str' != str ->
  t = lookup g str ->
  t = lookup ((str', t') :: g) str.
Proof.
move=> str'str tg /=; rewrite /lookup/=.
by case: ifPn => //=; rewrite (negbTE str'str).
Qed.

Definition recurse_tag g := Tag g.
Canonical found_tag g := recurse_tag g.

Canonical found str t g : find str t :=
  @Find str t (found_tag ((str, t) :: g))
              (@ctx_prf_head str t g).

Canonical recurse str t str' t' {H : infer (str' != str)}
    (g : find str t) : find str t :=
  @Find str t (recurse_tag ((str', t') :: untag (ctx_of g)))
    (@ctx_prf_tail str t (untag (ctx_of g)) str' t' H (ctx_prf g)).

End tagged_context.
Arguments lookup {T} t0 g str.
