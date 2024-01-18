Require Import String.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum ssrint interval.
From mathcomp Require Import mathcomp_extra boolp classical_sets.
From mathcomp Require Import functions cardinality fsbigop.
Require Import signed reals ereal topology normedtype sequences esum measure.
Require Import lebesgue_measure numfun lebesgue_integral itv kernel prob_lang.
Require Import lang_syntax_util exp.
From mathcomp Require Import ring lra.

(******************************************************************************)
(*       Syntax and Evaluation for a Probabilistic Programming Language       *)
(*                                                                            *)
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
(*            mkswap k == given a kernel k : (Y * X) ~> Z,                    *)
(*                        returns a kernel of type (X * Y) ~> Z               *)
(*              letin' := mkcomp \o mkswap                                    *)
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
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Reserved Notation "f .; g" (at level 60, right associativity,
  format "f  .; '/ '  g").
Reserved Notation "e -D> f ; mf" (at level 40).
Reserved Notation "e -P> k" (at level 40).

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(* TODO: mv *)
Arguments measurable_fst {d1 d2 T1 T2}.
Arguments measurable_snd {d1 d2 T1 T2}.

Section mswap.
Context d d' d3 (X : measurableType d) (Y : measurableType d')
  (Z : measurableType d3) (R : realType).
Variable k : R.-ker Y * X ~> Z.

Definition mswap xy U := k (swap xy) U.

Let mswap0 xy : mswap xy set0 = 0.
Proof. done. Qed.

Let mswap_ge0 x U : 0 <= mswap x U.
Proof. done. Qed.

Let mswap_sigma_additive x : semi_sigma_additive (mswap x).
Proof. exact: measure_semi_sigma_additive. Qed.

HB.instance Definition _ x := isMeasure.Build _ _ R
  (mswap x) (mswap0 x) (mswap_ge0 x) (@mswap_sigma_additive x).

Definition mkswap : _ -> {measure set Z -> \bar R} :=
  fun x => mswap x.

Let measurable_fun_kswap U :
  measurable U -> measurable_fun setT (mkswap ^~ U).
Proof.
move=> mU.
rewrite [X in measurable_fun _ X](_ : _ = k ^~ U \o @swap _ _)//.
apply measurableT_comp => //=; first exact: measurable_kernel.
exact: measurable_swap.
Qed.

HB.instance Definition _ := isKernel.Build _ _
  (X * Y)%type Z R mkswap measurable_fun_kswap.

End mswap.

Section mswap_sfinite_kernel.
Variables (d d' d3 : _) (X : measurableType d) (Y : measurableType d')
          (Z : measurableType d3) (R : realType).
Variable k : R.-sfker Y * X ~> Z.

Let mkswap_sfinite :
  exists2 k_ : (R.-ker X * Y ~> Z)^nat,
  forall n, measure_fam_uub (k_ n) &
  forall x U, measurable U -> mkswap k x U = kseries k_ x U.
Proof.
have [k_ /= kE] := sfinite_kernel k.
exists (fun n => mkswap (k_  n)).
  move=> n.
  have /measure_fam_uubP[M hM] := measure_uub (k_ n).
  by exists M%:num => x/=; exact: hM.
move=> xy U mU.
by rewrite /mswap/= kE.
Qed.

HB.instance Definition _ :=
  Kernel_isSFinite_subdef.Build _ _ _ Z R (mkswap k) mkswap_sfinite.

End mswap_sfinite_kernel.

Section kswap_finite_kernel_finite.
Context d d' d3 (X : measurableType d) (Y : measurableType d')
  (Z : measurableType d3) (R : realType)
  (k : R.-fker Y * X ~> Z).

Let mkswap_finite : measure_fam_uub (mkswap k).
Proof.
have /measure_fam_uubP[r hr] := measure_uub k.
apply/measure_fam_uubP; exists (PosNum [gt0 of r%:num%R]) => x /=.
exact: hr.
Qed.

HB.instance Definition _ :=
  Kernel_isFinite.Build _ _ _ Z R (mkswap k) mkswap_finite.

End kswap_finite_kernel_finite.

Notation "l .; k" := (mkcomp l (mkswap k)) : ereal_scope.

Section letin'.
Variables (d d' d3 : _) (X : measurableType d) (Y : measurableType d')
          (Z : measurableType d3) (R : realType).

Definition letin' (l : R.-sfker X ~> Y) (k : R.-sfker Y * X ~> Z) :=
  locked [the R.-sfker X ~> Z of l .; k].

Lemma letin'E (l : R.-sfker X ~> Y) (k : R.-sfker Y * X ~> Z) x U :
  letin' l k x U = \int[l x]_y k (y, x) U.
Proof. by rewrite /letin'; unlock. Qed.

Lemma letin'_letin (l : R.-sfker X ~> Y) (k : R.-sfker Y * X ~> Z) :
  letin' l k = letin l (mkswap k).
Proof. by rewrite /letin'; unlock. Qed.

End letin'.

Section letin'C.
Import Notations.
Context d d1 d' (X : measurableType d) (Y : measurableType d1)
  (Z : measurableType d') (R : realType).
Variables (t : R.-sfker Z ~> X)
          (u' : R.-sfker X * Z ~> Y)
          (u : R.-sfker Z ~> Y)
          (t' : R.-sfker Y * Z ~> X)
          (tt' : forall y, t =1 fun z => t' (y, z))
          (uu' : forall x, u =1 fun z => u' (x, z)).

Definition T' z : set X -> \bar R := t z.
Let T0 z : (T' z) set0 = 0. Proof. by []. Qed.
Let T_ge0 z x : 0 <= (T' z) x. Proof. by []. Qed.
Let T_semi_sigma_additive z : semi_sigma_additive (T' z).
Proof. exact: measure_semi_sigma_additive. Qed.
HB.instance Definition _ z := @isMeasure.Build _ X R (T' z) (T0 z) (T_ge0 z)
  (@T_semi_sigma_additive z).

Let sfinT z : sfinite_measure (T' z). Proof. exact: sfinite_kernel_measure. Qed.
HB.instance Definition _ z := @isSFinite.Build _ X R (T' z) (sfinT z).

Definition U' z : set Y -> \bar R := u z.
Let U0 z : (U' z) set0 = 0. Proof. by []. Qed.
Let U_ge0 z x : 0 <= (U' z) x. Proof. by []. Qed.
Let U_semi_sigma_additive z : semi_sigma_additive (U' z).
Proof. exact: measure_semi_sigma_additive. Qed.
HB.instance Definition _ z := @isMeasure.Build _ Y R (U' z) (U0 z) (U_ge0 z)
  (@U_semi_sigma_additive z).

Let sfinU z : sfinite_measure (U' z). Proof. exact: sfinite_kernel_measure. Qed.
HB.instance Definition _ z := @isSFinite.Build _ Y R (U' z) (sfinU z).

Lemma letin'C z A : measurable A ->
  letin' t
  (letin' u'
  (ret (measurable_fun_prod macc1of3' macc0of3'))) z A =
  letin' u
  (letin' t'
  (ret (measurable_fun_prod macc0of3' macc1of3'))) z A.
Proof.
move=> mA.
rewrite !letin'E.
under eq_integral.
  move=> x _.
  rewrite letin'E -uu'.
  under eq_integral do rewrite retE /=.
  over.
rewrite (sfinite_Fubini (T' z) (U' z) (fun x => \d_(x.1, x.2) A ))//; last first.
  apply/EFin_measurable_fun => /=; rewrite (_ : (fun x => _) = mindic R mA)//.
  by apply/funext => -[].
rewrite /=.
apply: eq_integral => y _.
by rewrite letin'E/= -tt'; apply: eq_integral => // x _; rewrite retE.
Qed.

End letin'C.
Arguments letin'C {d d1 d' X Y Z R} _ _ _ _.

Section letin'A.
Context d d' d1 d2 d3 (X : measurableType d) (Y : measurableType d')
  (T1 : measurableType d1) (T2 : measurableType d2) (T3 : measurableType d3)
  (R : realType).
Import Notations.
Variables (t : R.-sfker X ~> T1)
          (u : R.-sfker T1 * X ~> T2)
          (v : R.-sfker T2 * X ~> Y)
          (v' : R.-sfker T2 * (T1 * X) ~> Y)
          (vv' : forall y, v =1 fun xz => v' (xz.1, (y, xz.2))).

Lemma letin'A x A : measurable A ->
  letin' t (letin' u v') x A
  =
  (letin' (letin' t u) v) x A.
Proof.
move=> mA.
rewrite !letin'E.
under eq_integral do rewrite letin'E.
rewrite letin'_letin/=.
rewrite integral_kcomp; [|by []|].
  apply: eq_integral => z _.
  apply: eq_integral => y _.
  by rewrite (vv' z).
exact: measurableT_comp (@measurable_kernel _ _ _ _ _ v _ mA) _.
Qed.

End letin'A.

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
  iter_mprod (map measurable_of_typ l).

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

(* Import Notations. *)

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

Inductive exp : flag -> ctx -> typ -> Type :=
| exp_unit g : exp D g Unit
| exp_bool g : bool -> exp D g Bool
| exp_nat g : nat -> exp D g Nat
| exp_real g : R -> exp D g Real
| exp_pow g : nat -> exp D g Real -> exp D g Real
| exp_bin (b : binop) g : exp D g (type_of_binop b) ->
    exp D g (type_of_binop b) -> exp D g (type_of_binop b)
| exp_rel (r : relop) g : exp D g Nat ->
    exp D g Nat -> exp D g Bool
| exp_pair g t1 t2 : exp D g t1 -> exp D g t2 -> exp D g (Pair t1 t2)
| exp_proj1 g t1 t2 : exp D g (Pair t1 t2) -> exp D g t1
| exp_proj2 g t1 t2 : exp D g (Pair t1 t2) -> exp D g t2
| exp_var g str t : t = lookup Unit g str -> exp D g t
| exp_bernoulli g (r : {nonneg R}) (r1 : (r%:num <= 1)%R) :
    exp D g (Prob Bool)
| exp_bernoulli_trunc g :
    exp D g Real -> exp D g (Prob Bool)
| exp_binomial g (n : nat) (r : {nonneg R}) (r1 : (r%:num <= 1)%R) :
    exp D g (Prob Nat)
| exp_binomial_trunc g (n : nat) :
    exp D g Real -> exp D g (Prob Nat)
| exp_uniform g (a b : R) (ab0 : (0 < b - a)%R) : exp D g (Prob Real)
| exp_beta g (a b : nat) : exp D g (Prob Real)
| exp_poisson g : nat -> exp D g Real -> exp D g Real
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
Arguments exp_pow {R g}.
Arguments exp_bin {R} b {g} &.
Arguments exp_rel {R} r {g} &.
Arguments exp_pair {R g} & {t1 t2}.
Arguments exp_var {R g} _ {t} & H.
Arguments exp_bernoulli {R g}.
Arguments exp_bernoulli_trunc {R g} &.
Arguments exp_binomial {R g}.
Arguments exp_uniform {R g} &.
Arguments exp_beta {R g} &.
Arguments exp_binomial_trunc {R g} &.
Arguments exp_poisson {R g}.
Arguments exp_normalize {R g _}.
Arguments exp_letin {R g} & {_ _}.
Arguments exp_sample {R g} & {t}.
Arguments exp_score {R g}.
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
Notation "'return' e" := (@exp_return _ _ _ e)
  (in custom expr at level 6) : lang_scope.
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
  (in custom expr at level 5,
   x constr,
   f custom expr at level 5,
   left associativity) : lang_scope.
Notation "{ c }" := c (in custom expr, c constr) : lang_scope.
Notation "x" := x
  (in custom expr at level 0, x ident) : lang_scope.
Notation "'Sample' e" := (exp_sample e)
  (in custom expr at level 5) : lang_scope.
Notation "'Score' e" := (exp_score e)
  (in custom expr at level 5) : lang_scope.
Notation "'Normalize' e" := (exp_normalize e)
  (in custom expr at level 0) : lang_scope.
Notation "'if' e1 'then' e2 'else' e3" := (exp_if e1 e2 e3)
  (in custom expr at level 6) : lang_scope.

Section free_vars.
Context {R : realType}.

Fixpoint free_vars k g t (e : @exp R k g t) : seq string :=
  match e with
  | exp_unit _              => [::]
  | exp_bool _ _            => [::]
  | exp_nat _ _             => [::]
  | exp_real _ _            => [::]
  | exp_pow _ _ e           => free_vars e
  | exp_bin _ _ e1 e2    => free_vars e1 ++ free_vars e2
  | exp_rel _ _ e1 e2    => free_vars e1 ++ free_vars e2
  | exp_pair _ _ _ e1 e2    => free_vars e1 ++ free_vars e2
  | exp_proj1 _ _ _ e       => free_vars e
  | exp_proj2 _ _ _ e       => free_vars e
  | exp_var _ x _ _         => [:: x]
  | exp_bernoulli _ _ _     => [::]
  | exp_bernoulli_trunc _ e     => free_vars e
  | exp_binomial _ _ _ _     => [::]
  | exp_uniform _ _ _ _     => [::]
  | exp_beta _ _ _ => [::]
  | exp_binomial_trunc _ _ e     => free_vars e
  | exp_poisson _ _ e       => free_vars e
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
apply/prod_measurable_funP; split.
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
  Kernel_isSFinite_subdef.Build _ _ _ _ _ (@kweak g h x t f) sf.

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
Definition bernoulli0 := @bernoulli R 0%R%:nng ler01.

HB.instance Definition _ := Probability.on bernoulli0.

Lemma __ : Measurable.sort
                 (pprobability
                    [the measurableType (R.-ocitv.-measurable).-sigma of 
                    salgebraType (R.-ocitv.-measurable)] R) = 
Measurable.sort (@mtyp R (Prob Real)).
rewrite /=.
(* done. *)
Abort.

Inductive evalD : forall g t, exp D g t ->
  forall f : dval R g t, measurable_fun setT f -> Prop :=
| eval_unit g : ([TT] : exp D g _) -D> cst tt ; ktt

| eval_bool g b : ([b:B] : exp D g _) -D> cst b ; kb b

| eval_nat g n : ([n:N] : exp D g _) -D> cst n; kn n

| eval_real g r : ([r:R] : exp D g _) -D> cst r ; kr r

| eval_pow g n (e : exp D g _) f mf : e -D> f ; mf -> 
  [e ^+ {n}] -D> (fun x => f x ^+ n) ; (measurable_fun_pow n mf)

| eval_bin g bop (e1 : exp D g _) f1 mf1 e2 f2 mf2 :
  e1 -D> f1 ; mf1 -> e2 -D> f2 ; mf2 ->
  exp_bin bop e1 e2 -D> fun_of_binop f1 f2 ; mfun_of_binop mf1 mf2

| eval_rel g rop (e1 : exp D g _) f1 mf1 e2 f2 mf2 :
  e1 -D> f1 ; mf1 -> e2 -D> f2 ; mf2 ->
  exp_rel rop e1 e2 -D> fun_of_relop rop f1 f2 ; mfun_of_relop rop mf1 mf2

| eval_pair g t1 (e1 : exp D g t1) f1 mf1 t2 (e2 : exp D g t2) f2 mf2 :
  e1 -D> f1 ; mf1 -> e2 -D> f2 ; mf2 ->
  [(e1, e2)] -D> fun x => (f1 x, f2 x) ; measurable_fun_prod mf1 mf2

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

| eval_bernoulli g r r1 :
  (exp_bernoulli r r1 : exp D g _) -D> cst (bernoulli r1) ;
  measurable_cst _

| eval_bernoulli_trunc g e r mr :
  e -D> r ; mr ->
  (exp_bernoulli_trunc e : exp D g _) -D> bernoulli_trunc \o r ;
  measurableT_comp measurable_bernoulli_trunc mr

| eval_binomial g n (p : {nonneg R}) (p1 : (p%:num <= 1)%R) :
  (exp_binomial n p p1 : exp D g _) -D> cst (binomial_probability n p1) ;
                                        measurable_cst _

| eval_binomial_trunc g n e r mr :
  e -D> r ; mr ->
  (exp_binomial_trunc n e : exp D g _) -D> binomial_probability_trunc n \o r ;
  measurableT_comp (measurable_binomial_probability_trunc n) mr

| eval_uniform g (a b : R) (ab0 : (0 < b - a)%R) :
  (exp_uniform a b ab0 : exp D g _) -D> cst (uniform_probability ab0) ;
                                        measurable_cst _

| eval_beta g (a b : nat) (p : {nonneg R}) (p1 : (p%:num <= 1)%R) :
  (exp_beta a b : exp D g _) -D> cst (beta a b p1) ; measurable_cst _

| eval_poisson g n (e : exp D g _) f mf :
  e -D> f ; mf ->
  exp_poisson n e -D> poisson n \o f ;
                      measurableT_comp (measurable_poisson n) mf

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
- move=> g r r1 {}v {}mv.
  inversion 1; subst g0 r0.
  inj_ex H3; subst v.
  by have -> : r1 = r3 by [].
- move=> g e r mr ev IH {}v {}mv.
  inversion 1; subst g0.
  inj_ex H0; subst e0.
  inj_ex H4; subst v.
  by rewrite (IH _ _ H2).
- move=> g n p p1 {}v {}mv.
  inversion 1; subst g0 n0 p0.
  inj_ex H4; subst v.
  by have -> : p1 = p3 by [].
- move=> g n e f mf ev IH {}v {}mv.
  inversion 1; subst g0 n0.
  inj_ex H2; subst e0.
  inj_ex H4; subst v.
  inj_ex H5; subst mv.
  by rewrite (IH _ _ H3).
- move=> g a b ab0 {}v {}mv.
  inversion 1; subst g0 a0 b0.
  inj_ex H4; subst v.
  by have -> : ab0 = ab2.
- move=> g a b p p1 {}v {}mv.
  inversion 1. subst g0 a0 b0.
  inj_ex H2; subst v.
  inj_ex H4.
  have -> : p1 = p2 by [].
- move=> g t e0 k ev IH {}v {}mv.
  inversion 1; subst g0 t0.
  inj_ex H2; subst e0.
  inj_ex H4; subst v.
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
- move=> g r r1 {}v {}mv.
  inversion 1; subst g0 r0.
  inj_ex H3; subst v.
  by have -> : r1 = r3 by [].
- move=> g e r mr ev IH {}v {}mv.
  inversion 1; subst g0.
  inj_ex H0; subst e0.
  inj_ex H4; subst v.
  by rewrite (IH _ _ H2).
- move=> g n p p1 {}v {}mv.
  inversion 1; subst g0 n0 p0.
  inj_ex H4; subst v.
  by have -> : p1 = p3 by [].
- move=> g n e f mf ev IH {}v {}mv.
  inversion 1; subst g0 n0.
  inj_ex H2; subst e0.
  inj_ex H4; subst v.
  inj_ex H5; subst mv.
  by rewrite (IH _ _ H3).
- move=> g a b ab0 {}v {}mv.
  inversion 1; subst g0 a0 b0.
  inj_ex H4; subst v.
  by have -> : ab0 = ab2.
- move=> g n e f mf ev IH {}v {}mv.
  inversion 1; subst g0 n0.
  inj_ex H2; subst e0.
  inj_ex H4; subst v.
  inj_ex H5; subst mv.
  by rewrite (IH _ _ H3).
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
- move=> b g e1 [f1 [mf1 H1]] e2 [f2 [mf2 H2]].
  by exists (fun_of_binop f1 f2); eexists; exact: eval_bin.
- move=> r g e1 [f1 [mf1 H1]] e2 [f2 [mf2 H2]].
  by exists (fun_of_relop r f1 f2); eexists; exact: eval_rel.
- move=> g t1 t2 e1 [f1 [mf1 H1]] e2 [f2 [mf2 H2]].
  by exists (fun x => (f1 x, f2 x)); eexists; exact: eval_pair.
- move=> g t1 t2 e [f [mf H]].
  by exists (fst \o f); eexists; exact: eval_proj1.
- move=> g t1 t2 e [f [mf H]].
  by exists (snd \o f); eexists; exact: eval_proj2.
- by move=> g x t tE; subst t; eexists; eexists; exact: eval_var.
- by move=> r r1; eexists; eexists; exact: eval_bernoulli.
- move=> g e [p [mp H]].
  by exists (bernoulli_trunc \o p); eexists; exact: eval_bernoulli_trunc.
- by move=> p p1; eexists; eexists; exact: eval_binomial.
- move=> g n e [p [mp H]].
  exists (binomial_probability_trunc n \o p).
  eexists; exact: (eval_binomial_trunc n).
- by eexists; eexists; exact: eval_uniform.
- move=> g h e [f [mf H]].
  by exists (poisson h \o f); eexists; exact: eval_poisson.
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
  @existT _ _ (fun x => f x ^+ n) (measurable_fun_pow n mf).
Proof.
by move=> f mf; apply/execD_evalD/eval_pow/evalD_execD.
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

Lemma execD_pair g t1 t2 (e1 : exp D g t1) (e2 : exp D g t2) :
  let f1 := projT1 (execD e1) in let f2 := projT1 (execD e2) in
  let mf1 := projT2 (execD e1) in let mf2 := projT2 (execD e2) in
  execD [(e1, e2)] =
  @existT _ _ (fun z => (f1 z, f2 z))
              (@measurable_fun_prod _ _ _ (mctx g) (mtyp t1) (mtyp t2)
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

Lemma execD_bernoulli g r (r1 : (r%:num <= 1)%R) :
  @execD g _ (exp_bernoulli r r1) =
    existT _ (cst [the probability _ _ of bernoulli r1]) (measurable_cst _).
Proof. exact/execD_evalD/eval_bernoulli. Qed.

Lemma execD_bernoulli_trunc g e :
  @execD g _ (exp_bernoulli_trunc e) =
    existT _ (bernoulli_trunc \o projT1 (execD e)) (measurableT_comp measurable_bernoulli_trunc (projT2 (execD e))).
Proof. exact/execD_evalD/eval_bernoulli_trunc/evalD_execD. Qed.

Lemma execD_binomial g n p (p1 : (p%:num <= 1)%R) :
  @execD g _ (exp_binomial n p p1) =
    existT _ (cst [the probability _ _ of binomial_probability n p1]) (measurable_cst _).
Proof. exact/execD_evalD/eval_binomial. Qed.

Lemma execD_binomial_trunc g n e :
  @execD g _ (exp_binomial_trunc n e) =
    existT _ (binomial_probability_trunc n \o projT1 (execD e))
    (measurableT_comp (measurable_binomial_probability_trunc n) (projT2 (execD e))).
Proof. exact/execD_evalD/eval_binomial_trunc/evalD_execD. Qed.

Lemma execD_uniform g a b ab0 :
  @execD g _ (exp_uniform a b ab0) =
    existT _ (cst [the probability _ _ of uniform_probability ab0]) (measurable_cst _).
Proof. exact/execD_evalD/eval_uniform. Qed.

Lemma execD_normalize_pt g t (e : exp P g t) :
  @execD g _ [Normalize e] =
  existT _ (normalize_pt (execP e) : _ -> pprobability _ _)
           (measurable_normalize_pt (execP e)).
Proof. exact/execD_evalD/eval_normalize/evalP_execP. Qed.

Lemma execD_poisson g n (e : exp D g Real) :
  execD (exp_poisson n e) =
    existT _ (poisson n \o (projT1 (execD e)))
             (measurableT_comp (measurable_poisson n) (projT2 (execD e))).
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
