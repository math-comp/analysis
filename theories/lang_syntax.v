Require Import String.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp Require Import interval_inference.
From mathcomp Require Import unstable mathcomp_extra boolp classical_sets.
From mathcomp Require Import functions cardinality fsbigop.
From mathcomp Require Import reals ereal topology normedtype sequences exp.
From mathcomp Require Import esum measure lebesgue_measure numfun derive realfun.
From mathcomp Require Import lebesgue_integral probability ftc kernel charge.
From mathcomp Require Import prob_lang lang_syntax_util.

(**md**************************************************************************)
(* # Syntax and Evaluation for a Probabilistic Programming Language           *)
(*                                                                            *)
(* Reference:                                                                 *)
(* - R. Saito, R. Affeldt. Experimenting with an Intrinsically-Typed          *)
(*   Probabilistic Programming Language in Coq using s-finite kernels in Coq. *)
(*   APLAS 2023                                                               *)
(*                                                                            *)
(* beta distribution                                                          *)
(* ```                                                                        *)
(*            beta_pdf == probability density function for beta               *)
(*           beta_prob == beta probability measure                            *)
(* ```                                                                        *)
(*                                                                            *)
(* ```                                                                        *)
(*                 typ == syntax for types of data structures                 *)
(* measurable_of_typ t == the measurable type corresponding to type t         *)
(*                        It is of type {d & measurableType d}                *)
(*         mtyp_disp t == the display corresponding to type t                 *)
(*              mtyp t == the measurable type corresponding to type t         *)
(*                        It is of type measurableType (mtyp_disp t)          *)
(* measurable_of_seq s == the product space corresponding to the              *)
(*                        list s : seq typ                                    *)
(*                        It is of type {d & measurableType d}                *)
(*         acc_typ s n == function that access the nth element of s : seq typ *)
(*                        It is a function from projT2 (measurable_of_seq s)  *)
(*                        to projT2 (measurable_of_typ (nth Unit s n))        *)
(*                 ctx == type of context                                     *)
(*                     := seq (string * type)                                 *)
(*         mctx_disp g == the display corresponding to the context g          *)
(*              mctx g := the measurable type corresponding to the context g  *)
(*                        It is formed of nested pairings of measurable       *)
(*                        spaces. It is of type measurableType (mctx_disp g)  *)
(*                flag == a flag is either D (deterministic) or               *)
(*                        P (probabilistic)                                   *)
(*           exp f g t == syntax of expressions with flag f of type t         *)
(*                        context g                                           *)
(*          dval R g t == "deterministic value", i.e.,                        *)
(*                        function from mctx g to mtyp t                      *)
(*          pval R g t == "probabilistic value", i.e.,                        *)
(*                        s-finite kernel, from mctx g to mtyp t              *)
(*        e -D> f ; mf == the evaluation of the deterministic expression e    *)
(*                        leads to the deterministic value f                  *)
(*                        (mf is the proof that f is measurable)              *)
(*             e -P> k == the evaluation of the probabilistic function f      *)
(*                        leads to the probabilistic value k                  *)
(*             execD e == a dependent pair of a function corresponding to the *)
(*                        evaluation of e and a proof that this function is   *)
(*                        measurable                                          *)
(*             execP e == a s-finite kernel corresponding to the evaluation   *)
(*                        of the probabilistic expression e                   *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Reserved Notation "e -D> f ; mf" (at level 40).
Reserved Notation "e -P> k" (at level 40).

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(* In this module, we use our lemma continuous_FTC2 to compute the value of
 * integration of the indicator function over the interval [0, 1].
 * we can use our lemma continuous_FTC2 because it requires continuous
 * within [0, 1], which the indicator function satisfies.
 * we also shows that the indicator function is not continuous in [0, 1],
 * required by previous version of lemma continuous_FTC2. This shows that
 * our lemma continuous_FTC2 is
 * enough weak to be usable in practice.
 *)
Module integral_indicator_function.
Section integral_indicator_function.

Context {R : realType}.
Notation mu := lebesgue_measure.
Local Open Scope ereal_scope.
Implicit Types (f : R -> R) (a b : R).

Local Import set_interval.

Let uni := @indic R R `[0%R, 1%R]%classic.

Let integrable_uni : mu.-integrable setT (EFin \o uni).
Proof.
apply/integrableP; split.
  apply: measurableT_comp => //.
  exact: measurable_indic.
apply/abse_integralP => //.
  apply: measurableT_comp => //.
  exact: measurable_indic.
rewrite -ge0_fin_numE; last exact: abse_ge0.
rewrite abse_fin_num integral_indic// setIT.
by rewrite /= lebesgue_measure_itv ifT.
Qed.

Let cuni_within : {within `[0%R, 1%R], continuous uni}.
Proof.
apply/continuous_within_itvP => //; split.
- move=> x x01.
  apply: (@near_cst_continuous R R 1%R).
  near=> z.
  rewrite /uni indic_restrict patchE ifT//.
  rewrite inE/=.
  apply: subset_itv_oo_cc.
  near: z.
  exact: near_in_itvoo.
- rewrite (_: uni 0 = 1%R); last first.
    rewrite /uni indic_restrict patchE ifT//.
    by rewrite inE/= boundl_in_itv bnd_simp/=.
  apply: cvg_near_cst.
  near=> z.
  rewrite /uni indic_restrict patchE ifT// inE/= in_itv/=; apply/andP; split => //.
  near: z.
  exact: nbhs_right_le.
- rewrite (_:uni 1 = 1%R); last first.
    rewrite /uni indic_restrict patchE ifT//.
    by rewrite inE/= boundr_in_itv bnd_simp/=.
  apply: cvg_near_cst.
  near=> z.
  rewrite /uni indic_restrict patchE ifT// inE/= in_itv/=; apply/andP; split => //.
  near: z.
  exact: nbhs_left_ge.
Unshelve. all: end_near. Qed.

Example cuni : ~ {in `[0%R, 1%R], continuous uni}.
Proof.
rewrite -existsNE/=.
exists 0%R.
rewrite not_implyE; split; first by rewrite boundl_in_itv/= bnd_simp.
move/left_right_continuousP.
apply/not_andP; left.
move/(@cvgrPdist_le _ R^o).
apply/existsNP.
exists 2%:R^-1%R.
rewrite not_implyE; split; first by rewrite invr_gt0.
move=> [e /= e0].
move/(_ (-(e / 2))%R).
apply/not_implyP; split.
  rewrite /= sub0r opprK ger0_norm; last by rewrite divr_ge0// ltW.
  rewrite -{1}(add0r e).
  exact: (midf_lt e0).2.
apply/not_implyP; split.
  rewrite oppr_lt0.
  exact: divr_gt0.
apply/negP; rewrite -ltNge.
rewrite /uni !indic_restrict !patchE.
rewrite ifT; last by rewrite inE/= boundl_in_itv/= bnd_simp.
rewrite ifF; last first.
  apply: negbTE; apply/negP.
  rewrite inE/= in_itv/=.
  apply/negP; rewrite negb_and; apply/orP; left.
  by rewrite -ltNge oppr_lt0 divr_gt0.
rewrite /point/= {2}/1%R/= subr0.
rewrite ger0_norm//.
rewrite invf_lt1//.
rewrite {1}(_:1%R = 1%:R)//; apply: ltr_nat.
Qed.

Let dintuni : derivable_oo_LRcontinuous (@id R^o) 0 1.
Proof.
split.
- move=> x _.
  exact: derivable_id.
- exact: cvg_at_right_filter.
- exact: cvg_at_left_filter.
Qed.

Let intuni'uni : {in `]0%R, 1%R[, (@id R^o)^`() =1 uni}.
Proof.
move=> x x01.
rewrite derive1E derive_id.
rewrite /uni indic_restrict patchE ifT// inE/=.
exact: subset_itv_oo_cc.
Qed.

Lemma intuni1 : (\int[mu]_(x in `[0, 1]) uni x)%R = 1%R.
Proof.
rewrite [RHS](_:1%R = fine (1%:E))//; congr (fine _).
rewrite (continuous_FTC2 ltr01 cuni_within dintuni intuni'uni).
by rewrite sube0.
Qed.

End integral_indicator_function.
End integral_indicator_function.

(* TODO: naming *)
(* duplicated, cvg_compNP *)
(*
Lemma cvg_atNP {T : topologicalType} {R : numFieldType} (f : R -> T) (a : R) (l : T) :
  f x @[x --> a] --> l <-> (f \o -%R) x @[x --> (- a)%R] --> l.
Proof.
rewrite nbhsN.
have <-// : f x @[x --> a] = fmap [eta f \o -%R] ((- x)%R @[x --> a]).
by apply/seteqP; split=> A; move=> [/= e e0 H]; exists e => //= B /H/=; rewrite opprK.
Qed.
*)

Lemma derivable_oo_bnd_id {R : numFieldType} (a b : R) :
  derivable_oo_LRcontinuous (@id R^o) a b.
Proof.
by split => //;
  [exact/cvg_at_right_filter/cvg_id|exact/cvg_at_left_filter/cvg_id].
Qed.

Lemma derivable_oo_bndN {R : realFieldType} (f : R -> R^o) a b :
  derivable_oo_LRcontinuous f (- a) (- b) ->
  derivable_oo_LRcontinuous (f \o -%R) b a.
Proof.
move=> [dF cFa cFb].
have oppK : (-%R \o -%R) = @id R by apply/funext => x/=; rewrite opprK.
split.
- move=> x xba; apply/derivable1_diffP.
  apply/(@differentiable_comp _ _ R^o _ -%R f x) => //.
  by apply/derivable1_diffP/dF; rewrite oppr_itvoo 2!opprK.
- by apply/cvg_at_rightNP; rewrite -compA oppK.
- by apply/cvg_at_leftNP; rewrite -compA oppK.
Qed.

Module increasing_change_of_variables_from_decreasing.
Section lt0.
Context {R : realType}.
Notation mu := lebesgue_measure.
Implicit Types (F G f : R -> R) (a b : R).

Lemma continuous_withinN f a b : (a < b)%R ->
  {within `[(- b)%R, (- a)%R], continuous (f \o -%R)} ->
  {within `[a, b], continuous f}.
Proof.
move=> ab cf.
- apply/continuous_within_itvP (* TODO: us [/\ ...] *) => //.
- split; rewrite -ltrN2 in ab.
  + move=> x xab.
    move/continuous_within_itvP : cf => /(_ ab) [cf _ _].
    rewrite (_ : f = (f \o -%R) \o -%R); last first.
      by apply/funext => y; rewrite /= opprK.
    apply: continuous_comp; first exact: opp_continuous.
    by apply: cf; rewrite -oppr_itvoo opprK.
  + move/continuous_within_itvP : cf => /(_ ab) [_ _ cf].
    apply/cvg_at_rightNP.
    by rewrite /= opprK in cf.
  + move/continuous_within_itvP : cf => /(_ ab) [_ cf _].
    apply/cvg_at_leftNP.
    by rewrite /= opprK in cf.
Qed.

(* duplicated, integration_by_substitution_oppr *)
(*
Lemma oppr_change (f : R -> R) a b : (a < b)%R ->
  {within `[a, b], continuous f} ->
  \int[mu]_(x in `[a, b]) (f x)%:E =
  \int[mu]_(x in `[-%R b, -%R a]) ((f \o -%R) x)%:E.
Proof.
move=> ab cf.
have dN : ((-%R : R -> R^o)^`() = cst (-1) :> (R -> R))%R. (* TODO: lemma? *)
  by apply/funext => x/=; rewrite derive1E deriveN// derive_id.
rewrite integration_by_substitution_decreasing//.
- by apply: eq_integral => /= x _; rewrite dN/= opprK mulr1 -compA/= opprK.
- exact/ltW.
- by move=> x y _ _ yx; rewrite ltrN2.
- by move=> y yab; rewrite dN; exact: cvg_cst.
- by rewrite dN; exact: is_cvg_cst.
- by rewrite dN; exact: is_cvg_cst.
- by apply: (@derivable_oo_bndN _ id) => //; exact: derivable_oo_bnd_id.
- apply: continuous_withinN.
  + by rewrite ltrN2.
  + rewrite -(_ : f = (f \o -%R) \o -%R)//; last first.
      by apply/funext => y; rewrite /= opprK.
    by rewrite !opprK.
Qed.
*)

End lt0.
End increasing_change_of_variables_from_decreasing.

(* duplicated? *)
Lemma decreasing_nonincreasing {R : realType} (F : R -> R) (J : interval R) :
  {in J &, {homo F : x y /~ (x < y)%R}} ->
  {in J &, {homo F : x y /~ (x <= y)%R}}.
Proof.
move=> dF.
move=> x y x01 y01.
by rewrite le_eqVlt => /predU1P[->//|/dF] => /(_ x01 y01)/ltW.
Qed.

Local Close Scope ereal_scope.
Lemma cvg_comp_filter {R : realType} (f g : R -> R) (r l : R) :
  continuous f ->
  (f \o g) x @[x --> r] --> l ->
  f x @[x --> g r] --> l.
Proof.
move=> cf fgrl.
apply/(@cvgrPdist_le _ R^o) => /= e e0.
have e20 : 0 < e / 2 by rewrite divr_gt0.
move/(@cvgrPdist_le _ R^o) : fgrl => /(_ _ e20) fgrl.
have := cf (g r).
move=> /(@cvgrPdist_le _ R^o) => /(_ _ e20)[x x0]H.
exists (minr x (e/2)).
  by rewrite lt_min x0.
move=> z.
rewrite /ball_ /= => grze.
rewrite -[X in X - _](subrK (f (g r))).
rewrite -(addrA _ _ (- f z)).
apply: (le_trans (ler_normD _ _)).
rewrite (splitr e) lerD//.
  case: fgrl => d /= d0 K.
  apply: K.
  by rewrite /ball_/= subrr normr0.
apply: H => /=.
by rewrite (lt_le_trans grze)// ge_min lexx.
Qed.
Local Open Scope ereal_scope.

Lemma deriveX_idfun {R : realType} n x :
  'D_1 (@GRing.exp R^o ^~ n.+1) x = n.+1%:R *: (x ^+ n)%R.
Proof. by rewrite exp_derive /GRing.scale/= mulr1. Qed.

Lemma decreasing_onem {R : numDomainType} : {homo (fun x : R => (1 - x)%R) : x y /~ (x < y)%R}.
Proof.
move=> b a ab.
by rewrite -ltrN2 !opprB ltr_leB.
Qed.

Lemma integral_exprn {R : realType} n :
  fine (\int[lebesgue_measure]_(x in `[0%R, 1%R]) (x ^+ n)%:E) = n.+1%:R^-1%R :> R.
Proof.
pose F (x : R) : R^o := (n.+1%:R^-1 * x ^+ n.+1)%R.
have cX m : {in `[0%R, 1%R], continuous (fun x : R => x ^+ m)%R}.
  by move=> x x01; exact: exprn_continuous.
have cF0 : {for 0%R, continuous F}.
  apply: continuousM; first exact: cvg_cst.
  by apply: cX; rewrite /= in_itv/= lexx ler01.
have cF1 : {for 1%R, continuous F}.
  apply: continuousM; first exact: cvg_cst.
  by apply: cX; rewrite /= in_itv/= lexx ler01.
have dcF : derivable_oo_LRcontinuous F 0 1.
  split.
  - by move=> x x01; apply: derivableM => //; exact: exprn_derivable.
  - apply: continuous_cvg; first exact: mulrl_continuous.
    by apply/cvg_at_right_filter/cX; rewrite in_itv/= lexx ler01.
  - apply: continuous_cvg; first exact: mulrl_continuous.
    by apply/cvg_at_left_filter/cX; rewrite in_itv/= lexx ler01.
have dFE : {in `]0%R, 1%R[, F^`() =1 (fun x : R => x ^+ n : R)%R}.
  move=> x x01.
  rewrite derive1Ml; last exact: exprn_derivable.
  by rewrite derive1E deriveX_idfun mulrA mulVf// mul1r.
rewrite (@continuous_FTC2 _ (fun x : R => x ^+ n)%R F)//.
  by rewrite /F/= expr1n expr0n/= mulr1 mulr0 subr0.
by apply: continuous_subspaceT; exact: exprn_continuous.
Qed.

Local Open Scope ereal_scope.
Local Open Scope ring_scope.

Declare Scope lang_scope.
Delimit Scope lang_scope with P.

Section syntax_of_types.
Import Notations.
Context {R : realType}.

Inductive typ :=
| Unit | Bool | Nat | Real
| Pair : typ -> typ -> typ
| Prob : typ -> typ.

HB.instance Definition _ := gen_eqMixin typ.

Fixpoint measurable_of_typ (t : typ) : {d & measurableType d} :=
  match t with
  | Unit => existT _ _ munit
  | Bool => existT _ _ mbool
  | Nat => existT _ _ (nat : measurableType _)
  | Real => existT _ _
    [the measurableType _ of (@measurableTypeR R)]
    (* (Real_sort__canonical__measure_Measurable R) *)
  | Pair A B => existT _ _
      [the measurableType (projT1 (measurable_of_typ A),
                           projT1 (measurable_of_typ B)).-prod%mdisp of
      (projT2 (measurable_of_typ A) *
       projT2 (measurable_of_typ B))%type]
  | Prob A => existT _ _ (pprobability (projT2 (measurable_of_typ A)) R)
  end.

Definition mtyp_disp t : measure_display := projT1 (measurable_of_typ t).

Definition mtyp t : measurableType (mtyp_disp t) :=
  projT2 (measurable_of_typ t).

Definition measurable_of_seq (l : seq typ) : {d & measurableType d} :=
  iter_mprod (List.map measurable_of_typ l).

End syntax_of_types.
Arguments measurable_of_typ {R}.
Arguments mtyp {R}.
Arguments measurable_of_seq {R}.

Section accessor_functions.
Context {R : realType}.

(* NB: almost the same as acc (map (@measurable_of_typ R) s) n l,
   modulo commutativity of map and measurable_of_typ *)
Fixpoint acc_typ (s : seq typ) n :
  projT2 (@measurable_of_seq R s) ->
  projT2 (measurable_of_typ (nth Unit s n)) :=
  match s return
    projT2 (measurable_of_seq s) -> projT2 (measurable_of_typ (nth Unit s n))
  with
  | [::] => match n with | 0 => (fun=> tt) | m.+1 => (fun=> tt) end
  | a :: l => match n with
              | 0 => fst
              | m.+1 => fun H => @acc_typ l m H.2
              end
  end.

(*Definition acc_typ : forall (s : seq typ) n,
  projT2 (@measurable_of_seq R s) ->
  projT2 (@measurable_of_typ R (nth Unit s n)).
fix H 1.
intros s n x.
destruct s as [|s].
  destruct n as [|n].
    exact tt.
  exact tt.
destruct n as [|n].
  exact (fst x).
rewrite /=.
apply H.
exact: (snd x).
Show Proof.
Defined.*)

Lemma measurable_acc_typ (s : seq typ) n : measurable_fun setT (@acc_typ s n).
Proof.
elim: s n => //= h t ih [|m]; first exact: measurable_fst.
by apply: (measurableT_comp (ih _)); exact: measurable_snd.
Qed.

End accessor_functions.
Arguments acc_typ {R} s n.
Arguments measurable_acc_typ {R} s n.

Section context.
Variables (R : realType).
Definition ctx := seq (string * typ).

Definition mctx_disp (g : ctx) := projT1 (@measurable_of_seq R (map snd g)).

Definition mctx (g : ctx) : measurableType (mctx_disp g) :=
  projT2 (@measurable_of_seq R (map snd g)).

End context.
Arguments mctx {R}.

Section syntax_of_expressions.
Context {R : realType}.

Inductive flag := D | P.

(*
Section uniop.

Inductive uniop :=
| uniop_not
| uniop_neg | uniop_inv.

Definition type_of_uniop (u : uniop) : typ :=
match u with
| uniop_not => Bool
| uniop_neg => Real
| uniop_inv => Real
end.

Definition fun_of_uniop g (u : uniop) : (mctx g -> mtyp (type_of_uniop u)) ->
  @mctx R g -> @mtyp R (type_of_uniop u) :=
match u with
| uniop_not => (fun f x => f x && f x : mtyp Bool)
| uniop_neg => (fun f => (\- f)%R)
| uniop_inv => (fun f => (f ^-1)%R)
end.

Definition mfun_of_uniop g b
  (f : @mctx R g -> @mtyp R (type_of_uniop b)) (mf : measurable_fun setT f)
  measurable_fun [set: @mctx R g] (fun_of_uniop f).
destruct b.
exact: measurable_and mf1 mf2.
exact: measurable_or mf1 mf2.
exact: measurable_funD.
exact: measurable_funB.
exact: measurable_funM.
Defined.

End uniop.
*)

Section binop.

Inductive binop :=
| binop_and | binop_or
| binop_add | binop_minus | binop_mult.

Definition type_of_binop (b : binop) : typ :=
match b with
| binop_and => Bool
| binop_or => Bool
| binop_add => Real
| binop_minus => Real
| binop_mult => Real
end.

Definition fun_of_binop g (b : binop) : (mctx g -> mtyp (type_of_binop b)) ->
  (mctx g -> mtyp (type_of_binop b)) -> @mctx R g -> @mtyp R (type_of_binop b) :=
match b with
| binop_and => (fun f1 f2 x => f1 x && f2 x : mtyp Bool)
| binop_or => (fun f1 f2 x => f1 x || f2 x : mtyp Bool)
| binop_add => (fun f1 f2 => (f1 \+ f2)%R)
| binop_minus => (fun f1 f2 => (f1 \- f2)%R)
| binop_mult => (fun f1 f2 => (f1 \* f2)%R)
end.

Definition mfun_of_binop g b
  (f1 : @mctx R g -> @mtyp R (type_of_binop b)) (mf1 : measurable_fun setT f1)
  (f2 : @mctx R g -> @mtyp R (type_of_binop b)) (mf2 : measurable_fun setT f2) :
  measurable_fun [set: @mctx R g] (fun_of_binop f1 f2).
destruct b.
exact: measurable_and mf1 mf2.
exact: measurable_or mf1 mf2.
exact: measurable_funD.
exact: measurable_funB.
exact: measurable_funM.
Defined.

End binop.

(* TODO: rename *)
(* TODO: generalize? *)
Section relop.
Inductive relop :=
| relop_le | relop_lt | relop_eq .

Definition fun_of_relop g (r : relop) : (@mctx R g -> @mtyp R Nat) ->
  (mctx g -> mtyp Nat) -> @mctx R g -> @mtyp R Bool :=
match r with
| relop_le => (fun f1 f2 x => (f1 x <= f2 x)%N)
| relop_lt => (fun f1 f2 x => (f1 x < f2 x)%N)
| relop_eq => (fun f1 f2 x => (f1 x == f2 x)%N)
end.

Definition mfun_of_relop g r
  (f1 : @mctx R g -> @mtyp R Nat) (mf1 : measurable_fun setT f1)
  (f2 : @mctx R g -> @mtyp R Nat) (mf2 : measurable_fun setT f2) :
  measurable_fun [set: @mctx R g] (fun_of_relop r f1 f2).
destruct r.
exact: measurable_fun_leq.
exact: measurable_fun_ltn.
exact: measurable_fun_eqn.
Defined.

End relop.

Section relop_Real.
Inductive relop_real :=
| relop_real_le | relop_real_lt | relop_real_eq .

Definition fun_of_relop_real g (r : relop_real) : (@mctx R g -> @mtyp R Real) ->
  (mctx g -> mtyp Real) -> @mctx R g -> @mtyp R Bool :=
match r with
| relop_real_le => (fun f1 f2 x => (f1 x <= f2 x)%R)
| relop_real_lt => (fun f1 f2 x => (f1 x < f2 x)%R)
| relop_real_eq => (fun f1 f2 x => (f1 x == f2 x)%R)
end.

Definition mfun_of_relop_real g r
  (f1 : @mctx R g -> @mtyp R Real) (mf1 : measurable_fun setT f1)
  (f2 : @mctx R g -> @mtyp R Real) (mf2 : measurable_fun setT f2) :
  measurable_fun [set: @mctx R g] (fun_of_relop_real r f1 f2).
destruct r.
exact: measurable_fun_ler.
exact: measurable_fun_ltr.
exact: measurable_fun_eqr.
Defined.

End relop_Real.

Inductive exp : flag -> ctx -> typ -> Type :=
| exp_unit g : exp D g Unit
| exp_bool g : bool -> exp D g Bool
| exp_nat g : nat -> exp D g Nat
| exp_real g : R -> exp D g Real
| exp_pow g : nat -> exp D g Real -> exp D g Real (* TODO: nat should be at second *)
| exp_pow_real g : R (* base *) -> exp D g Real -> exp D g Real
| exp_bin (b : binop) g : exp D g (type_of_binop b) ->
    exp D g (type_of_binop b) -> exp D g (type_of_binop b)
| exp_rel (r : relop) g : exp D g Nat ->
    exp D g Nat -> exp D g Bool
| exp_rel_real (r : relop_real) g : exp D g Real ->
    exp D g Real -> exp D g Bool
| exp_pair g t1 t2 : exp D g t1 -> exp D g t2 -> exp D g (Pair t1 t2)
| exp_proj1 g t1 t2 : exp D g (Pair t1 t2) -> exp D g t1
| exp_proj2 g t1 t2 : exp D g (Pair t1 t2) -> exp D g t2
| exp_var g str t : t = lookup Unit g str -> exp D g t
| exp_bernoulli g : exp D g Real -> exp D g (Prob Bool)
| exp_binomial g (n : nat) : exp D g Real -> exp D g (Prob Nat)
| exp_uniform g (a b : R) (ab : (a < b)%R) : exp D g (Prob Real)
| exp_beta g (a b : nat) (* NB: should be R *) : exp D g (Prob Real)
| exp_poisson g : nat -> exp D g Real -> exp D g Real
| exp_normal g (s : R) (s0 : (s != 0)%R)
    : exp D g Real -> exp D g (Prob Real) (* NB: 0 < s *)
| exp_normalize g t : exp P g t -> exp D g (Prob t)
| exp_letin g t1 t2 str : exp P g t1 -> exp P ((str, t1) :: g) t2 ->
    exp P g t2
| exp_sample g t : exp D g (Prob t) -> exp P g t
| exp_score g : exp D g Real -> exp P g Unit
| exp_return g t : exp D g t -> exp P g t
| exp_if z g t : exp D g Bool -> exp z g t -> exp z g t -> exp z g t
| exp_weak z g h t x : exp z (g ++ h) t ->
  x.1 \notin dom (g ++ h) -> exp z (g ++ x :: h) t.
Arguments exp_var {g} _ {t}.

Definition exp_var' (str : string) (t : typ) (g : find str t) :=
  @exp_var (untag (ctx_of g)) str t (ctx_prf g).
Arguments exp_var' str {t} g.

Lemma exp_var'E str t (f : find str t) H :
  exp_var' str f = exp_var str H :> (@exp _ _ _).
Proof. by rewrite /exp_var'; congr exp_var. Qed.

End syntax_of_expressions.
Arguments exp {R}.
Arguments exp_unit {R g}.
Arguments exp_bool {R g}.
Arguments exp_nat {R g}.
Arguments exp_real {R g}.
Arguments exp_pow {R g} &.
Arguments exp_pow_real {R g} &.
Arguments exp_bin {R} b {g} &.
Arguments exp_rel {R} r {g} &.
Arguments exp_rel_real {R} r {g} &.
Arguments exp_pair {R g} & {t1 t2}.
Arguments exp_var {R g} _ {t} & H.
Arguments exp_bernoulli {R g} &.
Arguments exp_binomial {R g} &.
Arguments exp_uniform {R g} &.
Arguments exp_beta {R g} &.
Arguments exp_poisson {R g}.
Arguments exp_normal {R g _} &.
Arguments exp_normalize {R g _}.
Arguments exp_letin {R g} & {_ _}.
Arguments exp_sample {R g} & {t}.
Arguments exp_score {R g} &.
Arguments exp_return {R g} & {_}.
Arguments exp_if {R z g t} &.
Arguments exp_weak {R} z g h {t} x.
Arguments exp_var' {R} str {t} g &.

Declare Custom Entry expr.
Notation "[ e ]" := e (e custom expr at level 5) : lang_scope.
Notation "'TT'" := (exp_unit) (in custom expr at level 1) : lang_scope.
Notation "b ':B'" := (@exp_bool _ _ b%bool)
  (in custom expr at level 1) : lang_scope.
Notation "n ':N'" := (@exp_nat _ _ n%N)
  (in custom expr at level 1) : lang_scope.
Notation "r ':R'" := (@exp_real _ _ r%R)
  (in custom expr at level 1, format "r :R") : lang_scope.
Notation "e ^+ n" := (exp_pow n e)
  (in custom expr at level 1) : lang_scope.
Notation "e `^ r" := (exp_pow_real e r)
  (in custom expr at level 1) : lang_scope.
Notation "e1 && e2" := (exp_bin binop_and e1 e2)
  (in custom expr at level 2) : lang_scope.
Notation "e1 || e2" := (exp_bin binop_or e1 e2)
  (in custom expr at level 2) : lang_scope.
Notation "e1 + e2" := (exp_bin binop_add e1 e2)
  (in custom expr at level 3) : lang_scope.
Notation "e1 - e2" := (exp_bin binop_minus e1 e2)
  (in custom expr at level 3) : lang_scope.
Notation "e1 * e2" := (exp_bin binop_mult e1 e2)
  (in custom expr at level 2) : lang_scope.
Notation "e1 <= e2" := (exp_rel relop_le e1 e2)
  (in custom expr at level 2) : lang_scope.
Notation "e1 == e2" := (exp_rel relop_eq e1 e2)
  (in custom expr at level 4) : lang_scope.
Notation "e1 <=R e2" := (exp_rel_real relop_real_le e1 e2)
  (in custom expr at level 2) : lang_scope.
Notation "e1 ==R e2" := (exp_rel_real relop_real_eq e1 e2)
  (in custom expr at level 4) : lang_scope.
Notation "'return' e" := (@exp_return _ _ _ e)
  (in custom expr at level 7) : lang_scope.
(*Notation "% str" := (@exp_var _ _ str%string _ erefl)
  (in custom expr at level 1, format "% str") : lang_scope.*)
(* Notation "% str H" := (@exp_var _ _ str%string _ H)
  (in custom expr at level 1, format "% str H") : lang_scope. *)
Notation "# str" := (@exp_var' _ str%string _ _)
  (in custom expr at level 1, format "# str").
Notation "e :+ str" := (exp_weak _ [::] _ (str, _) e erefl)
  (in custom expr at level 1) : lang_scope.
Notation "( e1 , e2 )" := (exp_pair e1 e2)
  (in custom expr at level 1) : lang_scope.
Notation "\pi_1 e" := (exp_proj1 e)
  (in custom expr at level 1) : lang_scope.
Notation "\pi_2 e" := (exp_proj2 e)
  (in custom expr at level 1) : lang_scope.
Notation "'let' x ':=' e 'in' f" := (exp_letin x e f)
  (in custom expr at level 6,
   x constr,
   f custom expr at level 6,
   left associativity) : lang_scope.
Notation "{ c }" := c (in custom expr, c constr) : lang_scope.
Notation "x" := x
  (in custom expr at level 0, x ident) : lang_scope.
Notation "'Sample' e" := (exp_sample e)
  (in custom expr at level 6) : lang_scope.
Notation "'Score' e" := (exp_score e)
  (in custom expr at level 6) : lang_scope.
Notation "'Normalize' e" := (exp_normalize e)
  (in custom expr at level 0) : lang_scope.
Notation "'if' e1 'then' e2 'else' e3" := (exp_if e1 e2 e3)
  (in custom expr at level 7) : lang_scope.
Notation "( e )" := e
  (in custom expr at level 1) : lang_scope.

Section free_vars.
Context {R : realType}.

Fixpoint free_vars k g t (e : @exp R k g t) : seq string :=
  match e with
  | exp_unit _              => [::]
  | exp_bool _ _            => [::]
  | exp_nat _ _             => [::]
  | exp_real _ _            => [::]
  | exp_pow _ _ e           => free_vars e
  | exp_pow_real _ _ e      => free_vars e
  | exp_bin _ _ e1 e2    => free_vars e1 ++ free_vars e2
  | exp_rel _ _ e1 e2    => free_vars e1 ++ free_vars e2
  | exp_rel_real _ _ e1 e2    => free_vars e1 ++ free_vars e2
  | exp_pair _ _ _ e1 e2    => free_vars e1 ++ free_vars e2
  | exp_proj1 _ _ _ e       => free_vars e
  | exp_proj2 _ _ _ e       => free_vars e
  | exp_var _ x _ _         => [:: x]
  | exp_bernoulli _ e     => free_vars e
  | exp_binomial _ _ e     => free_vars e
  | exp_uniform _ _ _ _     => [::]
  | exp_beta _ _ _ => [::]
  | exp_poisson _ _ e       => free_vars e
  | exp_normal _ _ _ e          => free_vars e
  | exp_normalize _ _ e     => free_vars e
  | exp_letin _ _ _ x e1 e2 => free_vars e1 ++ rem x (free_vars e2)
  | exp_sample _ _ _        => [::]
  | exp_score _ e           => free_vars e
  | exp_return _ _ e        => free_vars e
  | exp_if _ _ _ e1 e2 e3   => free_vars e1 ++ free_vars e2 ++ free_vars e3
  | exp_weak _ _ _ _ x e _  => rem x.1 (free_vars e)
  end.

End free_vars.

Definition dval R g t := @mctx R g -> @mtyp R t.
Definition pval R g t := R.-sfker @mctx R g ~> @mtyp R t.


Section weak.
Context {R : realType}.
Implicit Types (g h : ctx) (x : string * typ).
Local Open Scope ring_scope.

Fixpoint mctx_strong g h x (f : @mctx R (g ++ x :: h)) : @mctx R (g ++ h) :=
  match g as g0 return mctx (g0 ++ x :: h) -> mctx (g0 ++ h) with
  | [::] => fun f0 : mctx ([::] ++ x :: h) => let (a, b) := f0 in (fun=> id) a b
  | a :: t => uncurry (fun a b => (a, @mctx_strong t h x b))
  end f.

Definition weak g h x t (f : dval R (g ++ h) t) : dval R (g ++ x :: h) t :=
  f \o @mctx_strong g h x.

Lemma measurable_fun_mctx_strong g h x :
  measurable_fun setT (@mctx_strong g h x).
Proof.
elim: g h x => [h x|x g ih h x0]; first exact: measurable_snd.
apply/measurable_fun_pairP; split.
- rewrite [X in measurable_fun _ X](_ : _ = fst)//.
  by apply/funext => -[].
- rewrite [X in measurable_fun _ X](_ : _ = @mctx_strong g h x0 \o snd).
    apply: measurableT_comp; last exact: measurable_snd.
    exact: ih.
  by apply/funext => -[].
Qed.

Lemma measurable_weak g h x t (f : dval R (g ++ h) t) :
  measurable_fun setT f -> measurable_fun setT (@weak g h x t f).
Proof.
move=> mf; apply: measurableT_comp; first exact: mf.
exact: measurable_fun_mctx_strong.
Qed.

Definition kweak g h x t (f : pval R (g ++ h) t)
    : @mctx R (g ++ x :: h) -> {measure set @mtyp R t -> \bar R} :=
  f \o @mctx_strong g h x.

Section kernel_weak.
Context g h x t (f : pval R (g ++ h) t).

Let mf U : measurable U -> measurable_fun setT (@kweak g h x t f ^~ U).
Proof.
move=> mU.
rewrite (_ : kweak _ ^~ U = f ^~ U \o @mctx_strong g h x)//.
apply: measurableT_comp => //; first exact: measurable_kernel.
exact: measurable_fun_mctx_strong.
Qed.

HB.instance Definition _ := isKernel.Build _ _ _ _ _ (@kweak g h x t f) mf.
End kernel_weak.

Section sfkernel_weak.
Context g h (x : string * typ) t (f : pval R (g ++ h) t).

Let sf : exists2 s : (R.-ker @mctx R (g ++ x :: h) ~> @mtyp R t)^nat,
  forall n, measure_fam_uub (s n) &
  forall z U, measurable U -> (@kweak g h x t f) z U = kseries s z U .
Proof.
have [s hs] := sfinite_kernel f.
exists (fun n => @kweak g h x t (s n)).
  by move=> n; have [M hM] := measure_uub (s n); exists M => x0; exact: hM.
by move=> z U mU; by rewrite /kweak/= hs.
Qed.

HB.instance Definition _ :=
  isSFiniteKernel_subdef.Build _ _ _ _ _ (@kweak g h x t f) sf.

End sfkernel_weak.

Section fkernel_weak.
Context g h x t (f : R.-fker @mctx R (g ++ h) ~> @mtyp R t).

Let uub : measure_fam_uub (@kweak g h x t f).
Proof. by have [M hM] := measure_uub f; exists M => x0; exact: hM. Qed.

HB.instance Definition _ := @Kernel_isFinite.Build _ _ _ _ _
  (@kweak g h x t f) uub.
End fkernel_weak.

End weak.
Arguments weak {R} g h x {t}.
Arguments measurable_weak {R} g h x {t}.
Arguments kweak {R} g h x {t}.

Section eval.
Context {R : realType}.
Implicit Type (g : ctx) (str : string).
Local Open Scope lang_scope.

Local Open Scope ring_scope.

(* TODO: PR *)
Lemma measurable_powRr b : measurable_fun setT (@powR R b).
Proof.
rewrite /powR.
apply: measurable_fun_if => //.
  rewrite preimage_true setTI/=.
   case: (b == 0); rewrite ?set_true ?set_false.
     apply: measurableT_comp => //.
     exact: measurable_fun_eqr.
   exact: measurable_fun_set0.
rewrite preimage_false setTI.
apply: measurableT_comp => //.
exact: mulrr_measurable.
Qed.

Inductive evalD : forall g t, exp D g t ->
  forall f : dval R g t, measurable_fun setT f -> Prop :=
| eval_unit g : ([TT] : exp D g _) -D> cst tt ; ktt

| eval_bool g b : ([b:B] : exp D g _) -D> cst b ; kb b

| eval_nat g n : ([n:N] : exp D g _) -D> cst n; kn n

| eval_real g r : ([r:R] : exp D g _) -D> cst r ; kr r

| eval_pow g n (e : exp D g _) f mf : e -D> f ; mf ->
  [e ^+ {n}] -D> (fun x => f x ^+ n) ; (measurable_funX n mf)

| eval_pow_real g (e : exp D g _) r f mf : e -D> f ; mf ->
  [{r} `^ e] -D> (fun x => r `^ (f x)) ; measurableT_comp (measurable_powRr r) mf

| eval_bin g bop (e1 : exp D g _) f1 mf1 e2 f2 mf2 :
  e1 -D> f1 ; mf1 -> e2 -D> f2 ; mf2 ->
  exp_bin bop e1 e2 -D> fun_of_binop f1 f2 ; mfun_of_binop mf1 mf2

| eval_rel g rop (e1 : exp D g _) f1 mf1 e2 f2 mf2 :
  e1 -D> f1 ; mf1 -> e2 -D> f2 ; mf2 ->
  exp_rel rop e1 e2 -D> fun_of_relop rop f1 f2 ; mfun_of_relop rop mf1 mf2

| eval_rel_real g rop (e1 : exp D g _) f1 mf1 e2 f2 mf2 :
  e1 -D> f1 ; mf1 -> e2 -D> f2 ; mf2 ->
  exp_rel_real rop e1 e2 -D> fun_of_relop_real rop f1 f2 ; mfun_of_relop_real rop mf1 mf2

| eval_pair g t1 (e1 : exp D g t1) f1 mf1 t2 (e2 : exp D g t2) f2 mf2 :
  e1 -D> f1 ; mf1 -> e2 -D> f2 ; mf2 ->
  [(e1, e2)] -D> fun x => (f1 x, f2 x) ; measurable_fun_pair mf1 mf2

| eval_proj1 g t1 t2 (e : exp D g (Pair t1 t2)) f mf :
  e -D> f ; mf ->
  [\pi_1 e] -D> fst \o f ; measurableT_comp measurable_fst mf

| eval_proj2 g t1 t2 (e : exp D g (Pair t1 t2)) f mf :
  e -D> f ; mf ->
  [\pi_2 e] -D> snd \o f ; measurableT_comp measurable_snd mf

(* | eval_var g str : let i := index str (dom g) in
  [% str] -D> acc_typ (map snd g) i ; measurable_acc_typ (map snd g) i *)

| eval_var g x H : let i := index x (dom g) in
  exp_var x H -D> acc_typ (map snd g) i ; measurable_acc_typ (map snd g) i

| eval_bernoulli g e r mr :
  e -D> r ; mr -> (exp_bernoulli e : exp D g _) -D> bernoulli_prob \o r ;
                  measurableT_comp measurable_bernoulli_prob mr

| eval_binomial g n e r mr :
  e -D> r ; mr -> (exp_binomial n e : exp D g _) -D> binomial_prob n \o r ;
                   measurableT_comp (measurable_binomial_prob n) mr

| eval_uniform g (a b : R) (ab : (a < b)%R) :
  (exp_uniform a b ab : exp D g _) -D> cst (uniform_prob ab) ;
                                       measurable_cst _

| eval_beta g (a b : nat) :
  (exp_beta a b : exp D g _) -D> cst (beta_prob a b) ; measurable_cst _

| eval_poisson g n (e : exp D g _) f mf :
  e -D> f ; mf ->
  exp_poisson n e -D> poisson_pmf ^~ n \o f ;
                      measurableT_comp (measurable_poisson_pmf n measurableT) mf

(* TODO *)
| eval_normal g s (s0 : (s != 0)%R) (e : exp D g _) r mr :
  e -D> r ; mr ->
  (exp_normal s0 e : exp D g _) -D>
     (fun x => @normal_prob _ (r x) s) ;
 measurableT_comp (measurable_normal_prob2 s0) mr

| eval_normalize g t (e : exp P g t) k :
  e -P> k ->
  [Normalize e] -D> normalize_pt k ; measurable_normalize_pt k

| evalD_if g t e f mf (e1 : exp D g t) f1 mf1 e2 f2 mf2 :
  e -D> f ; mf -> e1 -D> f1 ; mf1 -> e2 -D> f2 ; mf2 ->
  [if e then e1 else e2] -D> fun x => if f x then f1 x else f2 x ;
                             measurable_fun_ifT mf mf1 mf2

| evalD_weak g h t e x (H : x.1 \notin dom (g ++ h)) f mf :
  e -D> f ; mf ->
  (exp_weak _ g h x e H : exp _ _ t) -D> weak g h x f ;
                                         measurable_weak g h x f mf

where "e -D> v ; mv" := (@evalD _ _ e v mv)

with evalP : forall g t, exp P g t -> pval R g t -> Prop :=

| eval_letin g t1 t2 str (e1 : exp _ g t1) (e2 : exp _ _ t2) k1 k2 :
  e1 -P> k1 -> e2 -P> k2 ->
  [let str := e1 in e2] -P> letin' k1 k2

| eval_sample g t (e : exp _ _ (Prob t))
    (p : mctx g -> pprobability (mtyp t) R) mp :
  e -D> p ; mp -> [Sample e] -P> sample p mp

| eval_score g (e : exp _ g _) f mf :
  e -D> f ; mf -> [Score e] -P> kscore mf

| eval_return g t (e : exp D g t) f mf :
  e -D> f ; mf -> [return e] -P> ret mf

| evalP_if g t e f mf (e1 : exp P g t) k1 e2 k2 :
  e -D> f ; mf -> e1 -P> k1 -> e2 -P> k2 ->
  [if e then e1 else e2] -P> ite mf k1 k2

| evalP_weak g h t (e : exp P (g ++ h) t) x
    (H : x.1 \notin dom (g ++ h)) f :
  e -P> f ->
  exp_weak _ g h x e H -P> kweak g h x f

where "e -P> v" := (@evalP _ _ e v).

End eval.

Notation "e -D> v ; mv" := (@evalD _ _ _ e v mv) : lang_scope.
Notation "e -P> v" := (@evalP _ _ _ e v) : lang_scope.

Scheme evalD_mut_ind := Induction for evalD Sort Prop
with evalP_mut_ind := Induction for evalP Sort Prop.

(* properties of the evaluation relation *)
Section eval_prop.
Variables (R : realType).
Local Open Scope lang_scope.

Lemma evalD_uniq g t (e : exp D g t) (u v : dval R g t) mu mv :
  e -D> u ; mu -> e -D> v ; mv -> u = v.
Proof.
move=> hu.
apply: (@evalD_mut_ind R
  (fun g t (e : exp D g t) f mf (h1 : e -D> f; mf) =>
    forall v mv, e -D> v; mv -> f = v)
  (fun g t (e : exp P g t) u (h1 : e -P> u) =>
    forall v, e -P> v -> u = v)); last exact: hu.
all: (rewrite {g t e u v mu mv hu}).
- move=> g {}v {}mv.
  inversion 1; subst g0.
  by inj_ex H3.
- move=> g b {}v {}mv.
  inversion 1; subst g0 b0.
  by inj_ex H3.
- move=> g n {}v {}mv.
  inversion 1; subst g0 n0.
  by inj_ex H3.
- move=> g r {}v {}mv.
  inversion 1; subst g0 r0.
  by inj_ex H3.
- move=> g n e f mf ev IH {}v {}mv.
  inversion 1; subst g0 n0.
  inj_ex H4; subst v.
  inj_ex H2; subst e0.
  by move: H3 => /IH <-.
- move=> g e r f mf ev IH {}v {}mv.
  inversion 1; subst g0 r0.
  inj_ex H4; subst v.
  inj_ex H2; subst e0.
  by move: H3 => /IH <-.
- move=> g bop e1 f1 mf1 e2 f2 mf2 ev1 IH1 ev2 IH2 {}v {}mv.
  inversion 1; subst g0 bop0.
  inj_ex H10; subst v.
  inj_ex H5; subst e1.
  inj_ex H6; subst e5.
  by move: H4 H11 => /IH1 <- /IH2 <-.
- move=> g rop e1 f1 mf1 e2 f2 mf2 ev1 IH1 ev2 IH2 {}v {}mv.
  inversion 1; subst g0 rop0.
  inj_ex H5; subst v.
  inj_ex H1; subst e1.
  inj_ex H3; subst e3.
  by move: H6 H7 => /IH1 <- /IH2 <-.
- move=> g rop e1 f1 mf1 e2 f2 mf2 ev1 IH1 ev2 IH2 {}v {}mv.
  inversion 1; subst g0 rop0.
  inj_ex H5; subst v.
  inj_ex H1; subst e1.
  inj_ex H3; subst e3.
  by move: H6 H7 => /IH1 <- /IH2 <-.
- move=> g t1 e1 f1 mf1 t2 e2 f2 mf2 ev1 IH1 ev2 IH2 {}v {}mv.
  simple inversion 1 => //; subst g0.
  case: H3 => ? ?; subst t0 t3.
  inj_ex H4; case: H4 => He1 He2.
  inj_ex He1; subst e0.
  inj_ex He2; subst e3.
  inj_ex H5; subst v.
  by move=> /IH1 <- /IH2 <-.
- move=> g t1 t2 e f mf H ih v mv.
  inversion 1; subst g0 t3 t0.
  inj_ex H11; subst v.
  clear H9.
  inj_ex H7; subst e1.
  by rewrite (ih _ _ H4).
- move=> g t1 t2 e f mf H ih v mv.
  inversion 1; subst g0 t3 t0.
  inj_ex H11; subst v.
  clear H9.
  inj_ex H7; subst e1.
  by rewrite (ih _ _ H4).
- move=> g str H n {}v {}mv.
  inversion 1; subst g0.
  inj_ex H9; rewrite -H9.
  by inj_ex H10.
- move=> g e r mr ev IH {}v {}mv.
  inversion 1; subst g0.
  inj_ex H0; subst e0.
  inj_ex H3; subst v.
  by rewrite (IH _ _ H4).
- move=> g n e f mf ev IH {}v {}mv.
  inversion 1; subst g0 n0.
  inj_ex H2; subst e0.
  inj_ex H4; subst v.
  by rewrite (IH _ _ H5).
- move=> g a b ab {}v {}mv.
  inversion 1; subst g0 a0 b0.
  inj_ex H4; subst v.
  by have -> : ab = ab1.
- (* TODO: beta *) move=> g a b {}v {}mv.
  inversion 1; subst g0 a0 b0.
  by inj_ex H4; subst v.
- move=> g t e k mk ev IH {}v {}mv.
  inversion 1; subst g0 t.
  inj_ex H2; subst e0.
  inj_ex H4; subst v.
  by rewrite (IH _ _ H3).
- move=> g s s0 e r mr ev IH {}v {}mv.
  inversion 1; subst g0 s1.
  inj_ex H2; subst e0.
  inj_ex H3; subst v.
  by rewrite (IH _ _ H5).
- move=> g t e k ev IH f mf.
  inversion 1; subst g0 t0.
  inj_ex H2; subst e0.
  inj_ex H4; subst f.
  inj_ex H5; subst mf.
  by rewrite (IH _ H3).
- move=> g t e f mf e1 f1 mf1 e2 f2 mf2 ev ih ev1 ih1 ev2 ih2 v m.
  inversion 1; subst g0 t0.
  inj_ex H2; subst e0.
  inj_ex H6; subst e5.
  inj_ex H7; subst e6.
  inj_ex H9; subst v.
  clear H11.
  have ? := ih1 _ _ H12; subst f6.
  have ? := ih2 _ _ H13; subst f7.
  by rewrite (ih _ _ H5).
- move=> g h t e  x H f mf ef ih {}v {}mv.
  inversion 1; subst t0 g0 h0 x0.
  inj_ex H12; subst e1.
  inj_ex H14; subst v.
  clear H16.
  by rewrite (ih _ _ H5).
- move=> g t1 t2 x e1 e2 k1 k2 ev1 IH1 ev2 IH2 k.
  inversion 1; subst g0 t0 t3 x.
  inj_ex H7; subst k.
  inj_ex H6; subst e5.
  inj_ex H5; subst e4.
  by rewrite (IH1 _ H4) (IH2 _ H8).
- move=> g t e p mp ev IH k.
  inversion 1; subst g0.
  inj_ex H5; subst t0.
  inj_ex H5; subst e1.
  inj_ex H7; subst k.
  have ? := IH _ _ H3; subst p1.
  by have -> : mp = mp1 by [].
- move=> g e f mf ev IH k.
  inversion 1; subst g0.
  inj_ex H0; subst e0.
  inj_ex H4; subst k.
  have ? := IH _ _ H2; subst f1.
  by have -> : mf = mf0 by [].
- move=> g t e0 f mf ev IH k.
  inversion 1; subst g0 t0.
  inj_ex H5; subst e1.
  inj_ex H7; subst k.
  have ? := IH _ _ H3; subst f1.
  by have -> : mf = mf1 by [].
- move=> g t e f mf e1 k1 e2 k2 ev ih ev1 ih1 ev2 ih2 k.
  inversion 1; subst g0 t0.
  inj_ex H0; subst e0.
  inj_ex H1; subst e3.
  inj_ex H5; subst k.
  inj_ex H2; subst e4.
  have ? := ih _ _ H6; subst f1.
  have -> : mf = mf0 by [].
  by rewrite (ih1 _ H7) (ih2 _ H8).
- move=> g h t e x xgh k ek ih.
  inversion 1; subst x0 g0 h0 t0.
  inj_ex H13; rewrite -H13.
  inj_ex H11; subst e1.
  by rewrite (ih _ H4).
Qed.

Lemma evalP_uniq g t (e : exp P g t) (u v : pval R g t) :
  e -P> u -> e -P> v -> u = v.
Proof.
move=> eu.
apply: (@evalP_mut_ind R
  (fun g t (e : exp D g t) f mf (h : e -D> f; mf) =>
    forall v mv, e -D> v; mv -> f = v)
  (fun g t (e : exp P g t) u (h : e -P> u) =>
    forall v, e -P> v -> u = v)); last exact: eu.
all: rewrite {g t e u v eu}.
- move=> g {}v {}mv.
  inversion 1; subst g0.
  by inj_ex H3.
- move=> g b {}v {}mv.
  inversion 1; subst g0 b0.
  by inj_ex H3.
- move=> g n {}v {}mv.
  inversion 1; subst g0 n0.
  by inj_ex H3.
- move=> g r {}v {}mv.
  inversion 1; subst g0 r0.
  by inj_ex H3.
- move=> g n e f mf ev IH {}v {}mv.
  inversion 1; subst g0 n0.
  inj_ex H4; subst v.
  inj_ex H2; subst e0.
  by move: H3 => /IH <-.
- move=> g e b f mf ev IH {}v {}mv.
  inversion 1; subst g0 r.
  inj_ex H4; subst v.
  inj_ex H2; subst e0.
  by move: H3 => /IH <-.
- move=> g bop e1 f1 mf1 e2 f2 mf2 ev1 IH1 ev2 IH2 {}v {}mv.
  inversion 1; subst g0 bop0.
  inj_ex H10; subst v.
  inj_ex H5; subst e1.
  inj_ex H6; subst e5.
  by move: H4 H11 => /IH1 <- /IH2 <-.
- move=> g rop e1 f1 mf1 e2 f2 mf2 ev1 IH1 ev2 IH2 {}v {}mv.
  inversion 1; subst g0 rop0.
  inj_ex H5; subst v.
  inj_ex H1; subst e1.
  inj_ex H3; subst e3.
  by move: H6 H7 => /IH1 <- /IH2 <-.
- move=> g rop e1 f1 mf1 e2 f2 mf2 ev1 IH1 ev2 IH2 {}v {}mv.
  inversion 1; subst g0 rop0.
  inj_ex H5; subst v.
  inj_ex H1; subst e1.
  inj_ex H3; subst e3.
  by move: H6 H7 => /IH1 <- /IH2 <-.
- move=> g t1 e1 f1 mf1 t2 e2 f2 mf2 ev1 IH1 ev2 IH2 {}v {}mv.
  simple inversion 1 => //; subst g0.
  case: H3 => ? ?; subst t0 t3.
  inj_ex H4; case: H4 => He1 He2.
  inj_ex He1; subst e0.
  inj_ex He2; subst e3.
  inj_ex H5; subst v.
  move=> e1f0 e2f3.
  by rewrite (IH1 _ _ e1f0) (IH2 _ _ e2f3).
- move=> g t1 t2 e f mf H ih v mv.
  inversion 1; subst g0 t3 t0.
  inj_ex H11; subst v.
  clear H9.
  inj_ex H7; subst e1.
  by rewrite (ih _ _ H4).
- move=> g t1 t2 e f mf H ih v mv.
  inversion 1; subst g0 t3 t0.
  inj_ex H11; subst v.
  clear H9.
  inj_ex H7; subst e1.
  by rewrite (ih _ _ H4).
- move=> g str H n {}v {}mv.
  inversion 1; subst g0.
  inj_ex H9; rewrite -H9.
  by inj_ex H10.
- move=> g e r mr ev IH {}v {}mv.
  inversion 1; subst g0.
  inj_ex H0; subst e0.
  inj_ex H3; subst v.
  by rewrite (IH _ _ H4).
- move=> g n e f mf ev IH {}v {}mv.
  inversion 1; subst g0 n0.
  inj_ex H2; subst e0.
  inj_ex H4; subst v.
  by rewrite (IH _ _ H5).
- move=> g a b ab {}v {}mv.
  inversion 1; subst g0 a0 b0.
  inj_ex H4; subst v.
  by have -> : ab = ab1.
- (* TODO: beta case*) move=> g a b {}v {}mv.
  inversion 1; subst g0 a0 b0.
  by inj_ex H4; subst v.
- move=> g n e f mf ev IH {}v {}mv.
  inversion 1; subst g0 n0.
  inj_ex H2; subst e0.
  inj_ex H4; subst v.
  inj_ex H5; subst mv.
  by rewrite (IH _ _ H3).
- move=> g s s0 e r mr ev IH {}v {}mv.
  inversion 1; subst g0 s1.
  inj_ex H2; subst e0.
  inj_ex H3; subst v.
  by rewrite (IH _ _ H5).
- move=> g t e k ev IH {}v {}mv.
  inversion 1; subst g0 t0.
  inj_ex H2; subst e0.
  inj_ex H4; subst v.
  inj_ex H5; subst mv.
  by rewrite (IH _ H3).
- move=> g t e f mf e1 f1 mf1 e2 f2 mf2 ef ih ef1 ih1 ef2 ih2 {}v {}mv.
  inversion 1; subst g0 t0.
  inj_ex H2; subst e0.
  inj_ex H6; subst e5.
  inj_ex H7; subst e6.
  inj_ex H9; subst v.
  clear H11.
  have ? := ih1 _ _ H12; subst f6.
  have ? := ih2 _ _ H13; subst f7.
  by rewrite (ih _ _ H5).
- move=> g h t e x H f mf ef ih {}v {}mv.
  inversion 1; subst x0 g0 h0 t0.
  inj_ex H12; subst e1.
  inj_ex H14; subst v.
  clear H16.
  by rewrite (ih _ _ H5).
- move=> g t1 t2 x e1 e2 k1 k2 ev1 IH1 ev2 IH2 k.
  inversion 1; subst g0 x t3 t0.
  inj_ex H7; subst k.
  inj_ex H5; subst e4.
  inj_ex H6; subst e5.
  by rewrite (IH1 _ H4) (IH2 _ H8).
- move=> g t e p mp ep IH v.
  inversion 1; subst g0 t0.
  inj_ex H7; subst v.
  inj_ex H5; subst e1.
  have ? := IH _ _ H3; subst p1.
  by have -> : mp = mp1 by [].
- move=> g e f mf ev IH k.
  inversion 1; subst g0.
  inj_ex H0; subst e0.
  inj_ex H4; subst k.
  have ? := IH _ _ H2; subst f1.
  by have -> : mf = mf0 by [].
- move=> g t e f mf ev IH k.
  inversion 1; subst g0 t0.
  inj_ex H7; subst k.
  inj_ex H5; subst e1.
  have ? := IH _ _ H3; subst f1.
  by have -> : mf = mf1 by [].
- move=> g t e f mf e1 k1 e2 k2 ev ih ev1 ih1 ev2 ih2 k.
  inversion 1; subst g0 t0.
  inj_ex H0; subst e0.
  inj_ex H1; subst e3.
  inj_ex H5; subst k.
  inj_ex H2; subst e4.
  have ? := ih _ _ H6; subst f1.
  have -> : mf0 = mf by [].
  by rewrite (ih1 _ H7) (ih2 _ H8).
- move=> g h t e x xgh k ek ih.
  inversion 1; subst x0 g0 h0 t0.
  inj_ex H13; rewrite -H13.
  inj_ex H11; subst e1.
  by rewrite (ih _ H4).
Qed.

Lemma eval_total z g t (e : @exp R z g t) :
  (match z with
  | D => fun e => exists f mf, e -D> f ; mf
  | P => fun e => exists k, e -P> k
  end) e.
Proof.
elim: e.
all: rewrite {z g t}.
- by do 2 eexists; exact: eval_unit.
- by do 2 eexists; exact: eval_bool.
- by do 2 eexists; exact: eval_nat.
- by do 2 eexists; exact: eval_real.
- move=> g n e [f [mf H]].
  by exists (fun x => (f x ^+ n)%R); eexists; exact: eval_pow.
- move=> g r e [f [mf H]].
  by exists (fun x => (r `^ (f x))%R); eexists; exact: eval_pow_real.
- move=> b g e1 [f1 [mf1 H1]] e2 [f2 [mf2 H2]].
  by exists (fun_of_binop f1 f2); eexists; exact: eval_bin.
- move=> r g e1 [f1 [mf1 H1]] e2 [f2 [mf2 H2]].
  by exists (fun_of_relop r f1 f2); eexists; exact: eval_rel.
- move=> r g e1 [f1 [mf1 H1]] e2 [f2 [mf2 H2]].
  by exists (fun_of_relop_real r f1 f2); eexists; exact: eval_rel_real.
- move=> g t1 t2 e1 [f1 [mf1 H1]] e2 [f2 [mf2 H2]].
  by exists (fun x => (f1 x, f2 x)); eexists; exact: eval_pair.
- move=> g t1 t2 e [f [mf H]].
  by exists (fst \o f); eexists; exact: eval_proj1.
- move=> g t1 t2 e [f [mf H]].
  by exists (snd \o f); eexists; exact: eval_proj2.
- by move=> g x t tE; subst t; eexists; eexists; exact: eval_var.
- move=> g e [p [mp H]].
  exists ((bernoulli_prob : R -> pprobability bool R) \o p).
  by eexists; exact: eval_bernoulli.
- move=> g n e [p [mp H]].
  exists ((binomial_prob n : R -> pprobability nat R) \o p).
  by eexists; exact: (eval_binomial n).
- by eexists; eexists; exact: eval_uniform.
- by eexists; eexists; exact: eval_beta.
- move=> g h e [f [mf H]].
  by exists (poisson_pmf ^~ h \o f); eexists; exact: eval_poisson.
- move=> g s s0 e [r [mr H]].
  exists (fun x => @normal_prob _ (r x) s : pprobability _ _).
  by eexists; exact: eval_normal.
- move=> g t e [k ek].
  by exists (normalize_pt k); eexists; exact: eval_normalize.
- move=> g t1 t2 x e1 [k1 ev1] e2 [k2 ev2].
  by exists (letin' k1 k2); exact: eval_letin.
- move=> g t e [f [/= mf ef]].
  by eexists; exact: (@eval_sample _ _ _ _ _ mf).
- move=> g e [f [mf f_mf]].
  by exists (kscore mf); exact: eval_score.
- by move=> g t e [f [mf f_mf]]; exists (ret mf); exact: eval_return.
- case.
  + move=> g t e1 [f [mf H1]] e2 [f2 [mf2 H2]] e3 [f3 [mf3 H3]].
    by exists (fun g => if f g then f2 g else f3 g),
      (measurable_fun_ifT mf mf2 mf3); exact: evalD_if.
  + move=> g t e1 [f [mf H1]] e2 [k2 H2] e3 [k3 H3].
    by exists (ite mf k2 k3); exact: evalP_if.
- case=> [g h t x e [f [mf ef]] xgh|g h st x e [k ek] xgh].
  + by exists (weak _ _ _ f), (measurable_weak _ _ _ _ mf); exact/evalD_weak.
  + by exists (kweak _ _ _ k); exact: evalP_weak.
Qed.

Lemma evalD_total g t (e : @exp R D g t) : exists f mf, e -D> f ; mf.
Proof. exact: (eval_total e). Qed.

Lemma evalP_total g t (e : @exp R P g t) : exists k, e -P> k.
Proof. exact: (eval_total e). Qed.

End eval_prop.

Section execution_functions.
Local Open Scope lang_scope.
Context {R : realType}.
Implicit Type g : ctx.

Definition execD g t (e : exp D g t) :
    {f : dval R g t & measurable_fun setT f} :=
  let: exist _ H := cid (evalD_total e) in
  existT _ _ (projT1 (cid H)).

Lemma eq_execD g t (p1 p2 : @exp R D g t) :
  projT1 (execD p1) = projT1 (execD p2) -> execD p1 = execD p2.
Proof.
rewrite /execD /=.
case: cid => /= f1 [mf1 ev1].
case: cid => /= f2 [mf2 ev2] f12.
subst f2.
have ? : mf1 = mf2 by [].
subst mf2.
congr existT.
rewrite /sval.
case: cid => mf1' ev1'.
have ? : mf1 = mf1' by [].
subst mf1'.
case: cid => mf2' ev2'.
have ? : mf1 = mf2' by [].
by subst mf2'.
Qed.

Definition execP g t (e : exp P g t) : pval R g t :=
  projT1 (cid (evalP_total e)).

Lemma execD_evalD g t e x mx:
  @execD g t e = existT _ x mx <-> e -D> x ; mx.
Proof.
rewrite /execD; split.
  case: cid => x' [mx' H] [?]; subst x'.
  have ? : mx = mx' by [].
  by subst mx'.
case: cid => f' [mf' f'mf']/=.
move/evalD_uniq => /(_ _ _ f'mf') => ?; subst f'.
by case: cid => //= ? ?; congr existT.
Qed.

Lemma evalD_execD g t (e : exp D g t) :
  e -D> projT1 (execD e); projT2 (execD e).
Proof.
by rewrite /execD; case: cid => // x [mx xmx]/=; case: cid.
Qed.

Lemma execP_evalP g t (e : exp P g t) x :
  execP e = x <-> e -P> x.
Proof.
rewrite /execP; split; first by move=> <-; case: cid.
case: cid => // x0 Hx0.
by move/evalP_uniq => /(_ _ Hx0) ?; subst x.
Qed.

Lemma evalP_execP g t (e : exp P g t) : e -P> execP e.
Proof. by rewrite /execP; case: cid. Qed.

Lemma execD_unit g : @execD g _ [TT] = existT _ (cst tt) ktt.
Proof. exact/execD_evalD/eval_unit. Qed.

Lemma execD_bool g b : @execD g _ [b:B] = existT _ (cst b) (kb b).
Proof. exact/execD_evalD/eval_bool. Qed.

Lemma execD_nat g n : @execD g _ [n:N] = existT _ (cst n) (kn n).
Proof. exact/execD_evalD/eval_nat. Qed.

Lemma execD_real g r : @execD g _ [r:R] = existT _ (cst r) (kr r).
Proof. exact/execD_evalD/eval_real. Qed.

Local Open Scope ring_scope.
Lemma execD_pow g (e : exp D g _) n :
  let f := projT1 (execD e) in let mf := projT2 (execD e) in
  execD (exp_pow n e) =
  @existT _ _ (fun x => f x ^+ n) (measurable_funX n mf).
Proof.
by move=> f mf; apply/execD_evalD/eval_pow/evalD_execD.
Qed.

Lemma execD_pow_real g r (e : exp D g _) :
  let f := projT1 (execD e) in let mf := projT2 (execD e) in
  execD (exp_pow_real r e) =
  @existT _ _ (fun x => r `^ f x) (measurableT_comp (measurable_powRr r) mf).
Proof.
by move=> f mf; apply/execD_evalD/eval_pow_real/evalD_execD.
Qed.

Lemma execD_bin g bop (e1 : exp D g _) (e2 : exp D g _) :
  let f1 := projT1 (execD e1) in let f2 := projT1 (execD e2) in
  let mf1 := projT2 (execD e1) in let mf2 := projT2 (execD e2) in
  execD (exp_bin bop e1 e2) =
  @existT _ _ (fun_of_binop f1 f2) (mfun_of_binop mf1 mf2).
Proof.
by move=> f1 f2 mf1 mf2; apply/execD_evalD/eval_bin; exact/evalD_execD.
Qed.

Lemma execD_rel g rop (e1 : exp D g _) (e2 : exp D g _) :
  let f1 := projT1 (execD e1) in let f2 := projT1 (execD e2) in
  let mf1 := projT2 (execD e1) in let mf2 := projT2 (execD e2) in
  execD (exp_rel rop e1 e2) =
  @existT _ _ (fun_of_relop rop f1 f2) (mfun_of_relop rop mf1 mf2).
Proof.
by move=> f1 f2 mf1 mf2; apply/execD_evalD/eval_rel; exact: evalD_execD.
Qed.

Lemma execD_rel_real g rop (e1 : exp D g _) (e2 : exp D g _) :
  let f1 := projT1 (execD e1) in let f2 := projT1 (execD e2) in
  let mf1 := projT2 (execD e1) in let mf2 := projT2 (execD e2) in
  execD (exp_rel_real rop e1 e2) =
  @existT _ _ (fun_of_relop_real rop f1 f2) (mfun_of_relop_real rop mf1 mf2).
Proof.
by move=> f1 f2 mf1 mf2; apply/execD_evalD/eval_rel_real; exact: evalD_execD.
Qed.

Lemma execD_pair g t1 t2 (e1 : exp D g t1) (e2 : exp D g t2) :
  let f1 := projT1 (execD e1) in let f2 := projT1 (execD e2) in
  let mf1 := projT2 (execD e1) in let mf2 := projT2 (execD e2) in
  execD [(e1, e2)] =
  @existT _ _ (fun z => (f1 z, f2 z))
              (@measurable_fun_pair _ _ _ (mctx g) (mtyp t1) (mtyp t2)
              f1 f2 mf1 mf2).
Proof.
by move=> f1 f2 mf1 mf2; apply/execD_evalD/eval_pair; exact: evalD_execD.
Qed.

Lemma execD_proj1 g t1 t2 (e : exp D g (Pair t1 t2)) :
  let f := projT1 (execD e) in
  let mf := projT2 (execD e) in
  execD [\pi_1 e] = @existT _ _ (fst \o f)
                    (measurableT_comp measurable_fst mf).
Proof.
by move=> f mf; apply/execD_evalD/eval_proj1; exact: evalD_execD.
Qed.

Lemma execD_proj2 g t1 t2 (e : exp D g (Pair t1 t2)) :
  let f := projT1 (execD e) in let mf := projT2 (execD e) in
  execD [\pi_2 e] = @existT _ _ (snd \o f)
                    (measurableT_comp measurable_snd mf).
Proof.
by move=> f mf; apply/execD_evalD/eval_proj2; exact: evalD_execD.
Qed.

Lemma execD_var_erefl g str : let i := index str (dom g) in
  @execD g _ (exp_var str erefl) = existT _ (acc_typ (map snd g) i)
                      (measurable_acc_typ (map snd g) i).
Proof. by move=> i; apply/execD_evalD; exact: eval_var. Qed.

Lemma execD_var g x (H : nth Unit (map snd g) (index x (dom g)) = lookup Unit g x) :
  let i := index x (dom g) in
  @execD g _ (exp_var x H) = existT _ (acc_typ (map snd g) i)
                                      (measurable_acc_typ (map snd g) i).
Proof. by move=> i; apply/execD_evalD; exact: eval_var. Qed.

Lemma execD_bernoulli g e :
  @execD g _ (exp_bernoulli e) =
    existT _ ((bernoulli_prob : R -> pprobability bool R) \o projT1 (execD e))
             (measurableT_comp measurable_bernoulli_prob (projT2 (execD e))).
Proof. exact/execD_evalD/eval_bernoulli/evalD_execD. Qed.

Lemma execD_binomial g n e :
  @execD g _ (exp_binomial n e) =
    existT _ ((binomial_prob n : R -> pprobability nat R) \o projT1 (execD e))
             (measurableT_comp (measurable_binomial_prob n) (projT2 (execD e))).
Proof. exact/execD_evalD/eval_binomial/evalD_execD. Qed.

Lemma execD_uniform g a b ab0 :
  @execD g _ (exp_uniform a b ab0) =
    existT _ (cst [the probability _ _ of uniform_prob ab0]) (measurable_cst _).
Proof. exact/execD_evalD/eval_uniform. Qed.

Lemma execD_beta g a b :
  @execD g _ (exp_beta a b) =
    existT _ (cst [the probability _ _ of beta_prob a b]) (measurable_cst _).
Proof. exact/execD_evalD/eval_beta. Qed.

Lemma execD_normal g s s0 e :
  let f := projT1 (execD e) in let mf := projT2 (execD e) in
  @execD g _ (@exp_normal _ _ s s0 e) =
    existT _ (fun x => [the probability _ _ of @normal_prob _ (f x) s])
       (measurableT_comp (measurable_normal_prob2 s0) mf).
Proof. exact/execD_evalD/eval_normal/evalD_execD. Qed.

Lemma execD_normalize_pt g t (e : exp P g t) :
  @execD g _ [Normalize e] =
  existT _ (normalize_pt (execP e) : _ -> pprobability _ _)
           (measurable_normalize_pt (execP e)).
Proof. exact/execD_evalD/eval_normalize/evalP_execP. Qed.

Lemma execD_poisson g n (e : exp D g Real) :
  execD (exp_poisson n e) =
    existT _ (poisson_pmf ^~ n \o projT1 (execD e))
             (measurableT_comp (measurable_poisson_pmf n measurableT)
                               (projT2 (execD e))).
Proof. exact/execD_evalD/eval_poisson/evalD_execD. Qed.

Lemma execP_if g st e1 e2 e3 :
  @execP g st [if e1 then e2 else e3] =
  ite (projT2 (execD e1)) (execP e2) (execP e3).
Proof.
by apply/execP_evalP/evalP_if; [apply: evalD_execD| exact: evalP_execP..].
Qed.

Lemma execP_letin g x t1 t2 (e1 : exp P g t1) (e2 : exp P ((x, t1) :: g) t2) :
  execP [let x := e1 in e2] = letin' (execP e1) (execP e2) :> (R.-sfker _ ~> _).
Proof. by apply/execP_evalP/eval_letin; exact: evalP_execP. Qed.

Lemma execP_sample g t (e : @exp R D g (Prob t)) :
  let x := execD e in
  execP [Sample e] = sample (projT1 x) (projT2 x).
Proof. exact/execP_evalP/eval_sample/evalD_execD. Qed.

Lemma execP_score g (e : exp D g Real) :
  execP [Score e] = score (projT2 (execD e)).
Proof. exact/execP_evalP/eval_score/evalD_execD. Qed.

Lemma execP_return g t (e : exp D g t) :
  execP [return e] = ret (projT2 (execD e)).
Proof. exact/execP_evalP/eval_return/evalD_execD. Qed.

Lemma execP_weak g h x t (e : exp P (g ++ h) t)
    (xl : x.1 \notin dom (g ++ h)) :
  execP (exp_weak P g h _ e xl) = kweak _ _ _ (execP e).
Proof. exact/execP_evalP/evalP_weak/evalP_execP. Qed.

End execution_functions.
Arguments execD_var_erefl {R g} str.
Arguments execP_weak {R} g h x {t} e.
Arguments exp_var'E {R} str.

Local Open Scope lang_scope.
Lemma congr_letinl {R : realType} g t1 t2 str (e1 e2 : @exp _ _ g t1)
    (e : @exp _ _ (_ :: g) t2) x U :
    (forall y V, execP e1 y V = execP e2 y V) ->
  measurable U ->
  @execP R g t2 [let str := e1 in e] x U =
  @execP R g t2 [let str := e2 in e] x U.
Proof. by move=> + mU; move/eq_sfkernel => He; rewrite !execP_letin He. Qed.

Lemma congr_letinr {R : realType} g t1 t2 str (e : @exp _ _ _ t1)
  (e1 e2 : @exp _ _ (_ :: g) t2) x U :
  (forall y V, execP e1 (y, x) V = execP e2 (y, x) V) ->
  @execP R g t2 [let str := e in e1] x U = @execP R g t2 [let str := e in e2] x U.
Proof.
by move=> He; rewrite !execP_letin !letin'E; apply: eq_integral => ? _; exact: He.
Qed.

Lemma congr_normalize {R : realType} g t (e1 e2 : @exp R _ g t) :
  (forall x U, execP e1 x U = execP e2 x U) ->
  execD [Normalize e1] = execD [Normalize e2].
Proof.
move=> He; apply: eq_execD.
rewrite !execD_normalize_pt /=.
f_equal.
apply: eq_kernel => y V.
exact: He.
Qed.

Local Close Scope lang_scope.
