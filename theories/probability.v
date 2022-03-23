(* -*- company-coq-local-symbols: (("\\int_" . ?∫) ("'d" . ?𝑑) ("^\\+" . ?⁺) ("^\\-" . ?⁻) ("`&`" . ?∩) ("`|`" . ?∪) ("set0" . ?∅)); -*- *)
(* intersection U+2229; union U+222A, set U+2205 *)
(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg ssrnum ssrint interval.
Require Import boolp reals ereal.
From HB Require Import structures.
Require Import classical_sets signed topology normedtype sequences measure.
Require Import lebesgue_measure lebesgue_integral functions numfun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(******************************************************************************)
(*                             Probability (WIP)                              *)
(*                                                                            *)
(* measure_dirac                                                              *)
(* measure_image                                                              *)
(* probability                                                                *)
(* random_variable                                                            *)
(* expectation                                                                *)
(* distribution                                                               *)
(******************************************************************************)

(* TODO: move *)
Lemma preimage_setT {aT rT : Type} (f : aT -> rT) : f @^-1` setT = setT.
Proof. by []. Qed.
(* /TODO: move *)

Section measure_dirac.
Local Open Scope ereal_scope.
Variables (T : measurableType) (a : T) (R : realType).

Definition measure_dirac' (A : set T) : \bar R := (\1_A a)%:E.

Lemma measure_dirac'0 : measure_dirac' set0 = 0.
Proof. by rewrite /measure_dirac' indic0. Qed.

Lemma measure_dirac'_ge0 B : 0 <= measure_dirac' B.
Proof. by rewrite /measure_dirac' lee_fin. Qed.

Lemma measure_dirac'_sigma_additive : semi_sigma_additive measure_dirac'.
Proof.
move=> F mF tF mUF; rewrite /measure_dirac' indicE.
have [|aFn] /= := boolP (a \in \bigcup_n F n).
  rewrite inE => -[n _ Fna].
  have naF m : m != n -> a \notin F m.
    move=> mn; rewrite notin_set => Fma.
    move/trivIsetP : tF => /(_ _ _ Logic.I Logic.I mn).
    by rewrite predeqE => /(_ a)[+ _]; exact.
  apply/cvg_ballP => _/posnumP[e]; rewrite near_map; near=> m.
  have mn : (n < m)%N by near: m; exists n.+1.
  rewrite big_mkord (bigID (xpred1 (Ordinal mn)))//= big_pred1_eq/= big1/=.
    by rewrite adde0 (indicE (F n) a) mem_set//; exact: ballxx.
  by move=> j ij; rewrite indicE (negbTE (naF _ _)).
rewrite [X in X --> _](_ : _ = cst 0%E); first exact: cvg_cst.
rewrite funeqE => n /=; rewrite big1// => i _; rewrite indicE.
have [|//] := boolP (a \in F i); rewrite inE => Fia.
move: aFn; rewrite notin_set -[X in X -> _]/((~` (\bigcup_n0 F n0)) a).
by rewrite setC_bigcup => /(_ i Logic.I).
Unshelve. all: by end_near. Qed.

Definition measure_dirac : {measure set T -> \bar R} :=
  locked (Measure.Pack _ (Measure.Axioms
    measure_dirac'0 measure_dirac'_ge0 measure_dirac'_sigma_additive)).

Lemma measure_diracE A : measure_dirac A = (a \in A)%:R%:E.
Proof. by rewrite /measure_dirac; unlock. Qed.

End measure_dirac.
Arguments measure_dirac {T} _ {R}.

Require Import cardinality esum.
From mathcomp.finmap Require Import finmap.

(* TODO: awkward? *)
Lemma integralM_indic (T : measurableType) (R : realType)
    (m : {measure set T -> \bar R}) (D : set T) (f : R -> set T) k :
  (k < 0 -> f k = set0) ->
  measurable (f k) ->
  measurable D ->
  (\int_ D (k * \1_(f k) x)%:E 'd m[x] =
   k%:E * \int_ D (\1_(f k) x)%:E 'd m[x])%E.
Proof.
move=> fk0 mfk mD; have [k0|k0] := ltP k 0.
  rewrite (eq_integral (cst 0%E)) ?integral0 ?mule0; last first.
    move=> x _.
    by rewrite fk0// indic0 mulr0.
  rewrite (eq_integral (cst 0%E)) ?integral0 ?mule0// => x _.
  by rewrite fk0// indic0.
under eq_integral do rewrite EFinM.
rewrite ge0_integralM//.
- apply/EFin_measurable_fun/(@measurable_funS _ _ setT) => //.
  by rewrite (_ : \1_(f k) = mindic R mfk).
- by move=> y _; rewrite lee_fin.
Qed.

Lemma integralM_indic' (T : measurableType) (R : realType)
    (m : {measure set T -> \bar R}) (D : set T) (f : {nnsfun T >-> R}) k :
  measurable D ->
  (\int_ D (k * \1_(f @^-1` [set k]) x)%:E 'd m[x] =
   k%:E * \int_ D (\1_(f @^-1` [set k]) x)%:E 'd m[x])%E.
Proof.
move=> mD.
rewrite (@integralM_indic _ _ _ _ (fun k => f @^-1` [set k]))// => k0.
by rewrite preimage_nnfun0.
Qed.

Section integral_dirac.
Variables (T : measurableType) (a : T) (R : realType).
Variables (f : T -> R) (mf : measurable_fun setT (EFin \o f)).
Hypothesis f0 : forall x, (0 <= f x)%R.

Lemma integral_dirac :
  (\int_ setT (f x)%:E 'd (measure_dirac a)[x] = (f a)%:E)%E.
Proof.
have [f_ [ndf_ f_f]] := approximation measurableT mf (fun t _ => f0 t).
transitivity (lim (fun n => \int_ setT (f_ n x)%:E 'd (measure_dirac a)[x]))%E.
  rewrite -monotone_convergence//.
  - by apply: eq_integral => x _; apply/esym/cvg_lim => //; exact: f_f.
  - by move=> n; apply/EFin_measurable_fun; exact/(@measurable_funS _ _ setT).
  - by move=> *; rewrite lee_fin.
  - by move=> x _ m n mn; rewrite lee_fin; exact/lefP/ndf_.
rewrite (_ : (fun _ => _) = (fun n => (f_ n a)%:E)).
  by apply/cvg_lim => //; exact: f_f.
rewrite funeqE => n.
under eq_integral do rewrite fimfunE -sumEFin.
rewrite ge0_integral_sum//; last 2 first.
  - move=> r; apply/EFin_measurable_fun.
    apply: measurable_funM => //; first exact: measurable_fun_cst.
    by rewrite (_ : \1_ _ = mindic R (measurable_sfunP (f_ n) r)).
  - by move=> r x _; rewrite muleindic_ge0.
under eq_bigr; first by move=> r _; rewrite integralM_indic'//; over.
rewrite /= (big_fsetD1 (f_ n a))/=; last first.
  by rewrite in_fset_set// in_setE; exists a.
rewrite integral_indic// measure_diracE setIT mem_set// mule1.
rewrite big1_fset ?adde0// => r; rewrite !inE => /andP[rfna _] _.
rewrite integral_indic// measure_diracE setIT memNset ?mule0//=.
by move=> /esym; apply/eqP.
Qed.

End integral_dirac.

Section measure_image.
Local Open Scope ereal_scope.
Variables (T1 T2 : measurableType) (f : T1 -> T2).
Hypothesis mf : measurable_fun setT f.
Variables (R : realType) (m : {measure set T1 -> \bar R}).

Definition measure_image' A := m (f @^-1` A).

Lemma measure_image'0 : measure_image' set0 = 0.
Proof. by rewrite /measure_image' preimage_set0 measure0. Qed.

Lemma measure_image'_ge0 A : 0 <= measure_image' A.
Proof. by apply: measure_ge0; rewrite -[X in measurable X]setIT; apply: mf. Qed.

Lemma measure_image'_sigma_additive : semi_sigma_additive measure_image'.
Proof.
move=> F mF tF mUF; rewrite /measure_image' preimage_bigcup.
apply: measure_semi_sigma_additive.
- by move=> n; rewrite -[X in measurable X]setTI; exact: mf.
- apply/trivIsetP => /= i j _ _ ij; rewrite -preimage_setI.
  by move/trivIsetP : tF => /(_ _ _ _ _ ij) ->//; rewrite preimage_set0.
- by rewrite -preimage_bigcup -[X in measurable X]setTI; exact: mf.
Qed.

Definition measure_image : {measure set T2 -> \bar R} :=
  locked (Measure.Pack _ (Measure.Axioms
    measure_image'0 measure_image'_ge0 measure_image'_sigma_additive)).

Lemma measure_imageE A : measure_image A = m (f @^-1` A).
Proof. by rewrite /measure_image; unlock. Qed.

End measure_image.

Section transfer.
Local Open Scope ereal_scope.
Variables (T1 T2 : measurableType) (phi : T1 -> T2) (pt1 : T1).
Hypothesis mphi : measurable_fun setT phi.
Variables (R : realType) (mu : {measure set T1 -> \bar R}).

Lemma transfer (f : T2 -> \bar R) :
  measurable_fun setT f -> (forall y, 0 <= f y) ->
  \int_ setT (f y) 'd (measure_image mphi mu)[y] =
  \int_ setT ((f \o phi) x) 'd mu[x].
Proof.
move=> mf f0.
pose pt2 := phi pt1.
have [f_ [ndf_ f_f]] := approximation measurableT mf (fun t _ => f0 t).
transitivity
    (lim (fun n => \int_ setT (f_ n x)%:E 'd (measure_image mphi mu)[x])).
  rewrite -monotone_convergence//.
  - by apply: eq_integral => y _; apply/esym/cvg_lim => //; exact: f_f.
  - by move=> n; exact/EFin_measurable_fun.
  - by move=> n y _; rewrite lee_fin.
  - by move=> y _ m n mn; rewrite lee_fin; apply/lefP/ndf_.
rewrite (_ : (fun _ => _) =
    (fun n => \int_ setT ((EFin \o f_ n \o phi) x) 'd mu[x])).
  rewrite -monotone_convergence//; last 3 first.
    - move=> n /=; apply: measurable_fun_comp; first exact: measurable_fun_EFin.
      by apply: measurable_fun_comp => //; exact: measurable_sfun.
    - by move=> n x _ /=; rewrite lee_fin.
    - by move=> x _ m n mn; rewrite lee_fin; exact/lefP/ndf_.
  by apply: eq_integral => x _ /=; apply/cvg_lim => //; exact: f_f.
rewrite funeqE => n.
have mfnphi : forall r, measurable (f_ n @^-1` [set r] \o phi).
  move=> r.
  rewrite -[_ \o _]/(phi @^-1` (f_ n @^-1` [set r])) -(setTI (_ @^-1` _)).
  exact/mphi.
transitivity (\sum_(k <- fset_set [set of f_ n])
  \int (k * \1_(((f_ n) @^-1` [set k]) \o phi) x)%:E 'd mu[x]).
  under eq_integral do rewrite fimfunE -sumEFin.
  rewrite ge0_integral_sum//; last 2 first.
    - move=> y; apply/EFin_measurable_fun; apply: measurable_funM.
        exact: measurable_fun_cst.
      by rewrite (_ : \1_ _ = mindic R (measurable_sfunP (f_ n) y)).
    - by move=> y x _; rewrite muleindic_ge0.
  apply eq_bigr => r _; rewrite integralM_indic'// integral_indic//.
  rewrite measure_imageE.
  rewrite (@integralM_indic _ _ _ _ (fun r => f_ n @^-1` [set r] \o phi))//.
    by congr (_ * _)%E; rewrite [RHS](@integral_indic).
  by move=> r0; rewrite preimage_nnfun0.
rewrite -ge0_integral_sum//; last 2 first.
  - move=> r; apply/EFin_measurable_fun; apply: measurable_funM.
      exact: measurable_fun_cst.
    by rewrite (_ : \1_ _ = mindic R (mfnphi r)).
  - by move=> r x _; rewrite muleindic_ge0.
by apply eq_integral => x _; rewrite sumEFin -fimfunE.
Qed.

End transfer.

Module Probability.
Section probability.
Variable (R : realType).
Record t := mk {
  T : measurableType ;
  P : {measure set T -> \bar R} ;
  _ : P setT = 1%E }.
End probability.
Module Exports.
Definition probability (R : realType) := (t R).
Coercion T : t >-> measurableType.
Coercion P : t >-> Measure.map.
End Exports.
End Probability.
Export Probability.Exports.

Section probability_lemmas.
Variables (R : realType) (P : probability R).

Lemma probability_setT : P setT = 1%:E.
Proof. by case: P. Qed.

Lemma probability_set0 : P set0 = 0%:E.
Proof. exact: measure0. Qed.

Lemma probability_not_empty : @setT P !=set0.
Proof.
apply/set0P/negP => /eqP setT0.
have := probability_set0.
rewrite -setT0 probability_setT.
by apply/eqP; rewrite oner_neq0.
Qed.

End probability_lemmas.

Module RandomVariable.
Section randomvariable.
Variables (R : realType) (P : probability R).
Record t := mk {
  f : P -> R ;
  mf : measurable_fun setT f }.
End randomvariable.
Module Exports.
Section exports.
Variables (R : realType) (P : probability R).
Definition random_variable := t P.
Coercion f : t >-> Funclass.
End exports.
End Exports.
End RandomVariable.
Export RandomVariable.Exports.

Reserved Notation "'`E' X" (format "'`E'  X", at level 5).

Section expectation.
Local Open Scope ereal_scope.
Variables (R : realType) (P : probability R).

Definition expectation (X : random_variable P) := \int (X w)%:E 'd P[w].

Local Notation "'`E' X" := (expectation X).

End expectation.
Notation "'`E' X" := (expectation X).

Reserved Notation "'`V' X" (format "'`V'  X", at level 5).
Reserved Notation "X '`^2' " (at level 49).

Section distribution.
Variables (R : realType) (P : probability R) (X : random_variable P).

Definition distribution : {measure set R -> \bar R} :=
  measure_image (RandomVariable.mf X) P.

Lemma distribution_is_probability : distribution setT = 1%:E.
Proof.
by rewrite /distribution /= measure_imageE preimage_setT probability_setT.
Qed.

End distribution.

Section transfer_probability.
Local Open Scope ereal_scope.
Variables (R : realType) (P : probability R) (X : random_variable P).

Lemma transfer_probability (f : R -> \bar R) :
  measurable_fun setT f -> (forall y, 0 <= f y) ->
  \int_ setT (f y) 'd (distribution X)[y] =
  \int_ setT ((f \o X) x) 'd P[x].
Proof.
move=> mf f0; rewrite transfer//.
by have /cid[+ _] := probability_not_empty P; exact.
Qed.

End transfer_probability.
