(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum matrix.
From mathcomp Require Import interval rat generic_quotient.
Require Import mathcomp_extra boolp reals ereal set_interval classical_sets.
Require Import signed functions topology normedtype landau sequences derive.
Require Import realfun.
From HB Require Import structures.

Add Search Blacklist "__canonical__".
Add Search Blacklist "__functions_".
Add Search Blacklist "_factory_".
Add Search Blacklist "_mixin_".

(******************************************************************************)
(*              Definitions and lemmas for homotopy theory                    *)
(*                                                                            *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope quotient_scope.

HB.mixin Record IsContinuous {T U : topologicalType} (A : set T) (f : T -> U) :=
  { continuous_fun : {within A, continuous f }}.

HB.structure Definition JustContinuous {T U : topologicalType} A
  := {f of @IsContinuous T U A f}.

HB.structure Definition ContinuousFun {T U : topologicalType} 
    (A : set T) (B : set U) := 
  {f of @IsContinuous T U A f & @Fun T U A B f}.

Notation "{ 'continuous' A >-> B }" := 
  (@ContinuousFun.type _ _ A B) : form_scope.
Notation "[ 'continuous' 'of' f ]" := 
  ([the (@ContinuousFun.type _ _ _ _) of (f: _ -> _)]) : form_scope.

Canonical continuous_eq {T U : topologicalType} (A : set T) (B : set U) := 
  EqType  {continuous A >-> B} gen_eqMixin.
Canonical continuous_choice {T U : topologicalType} (A : set T) (B : set U) := 
  ChoiceType {continuous A >-> B} gen_choiceMixin .

HB.mixin Record IsParametrization {R : realType} (f : R -> R) := 
  { 
    parametrize_init : f 0 = 0;
    parametrize_final : f 1 = 1;
  }.

HB.structure Definition JustParametrization {R : realType} 
  := {f of @IsParametrization R f}.

HB.structure Definition Parametrization {R : realType}
  := {f of @IsParametrization R f & 
           @IsContinuous R R `[0,1]%classic f & 
           @Fun R R `[0,1]%classic `[0,1]%classic f }.

HB.structure Definition InjParametrization {R : realType}
  := {f of @Parametrization R f & 
           @SplitInj R R `[0,1]%classic f }.

Notation "{ 'parametrization' R }" := (@Parametrization.type R) : form_scope.
Notation "[ 'parametrization' 'of' f ]" := 
  ([the (@Parametrization.type _) of (f: _ -> _)]) : form_scope.

Notation "{ 'inj_parametrization' R }" := (@InjParametrization.type R) : form_scope.
Notation "[ 'inj_parametrization' 'of' f ]" := 
  ([the (@InjParametrization.type _) of (f: _ -> _)]) : form_scope.

Section continuous_hb_basics.
Section composition.
Context {T U V : topologicalType} {A : set T} {B : set U} {C : set V}.

Local Lemma comp_continuous (f : {continuous A >-> B}) (g : {continuous B >-> C}) :
  IsContinuous _ _ A (g \o f).
Proof. split => x; apply: (@continuous_comp
    (subspace_topologicalType A) (subspace_topologicalType B) _).
  exact/subspaceT_continuous/continuous_fun.
exact: continuous_fun.
Qed.

HB.instance Definition funcomp f g := comp_continuous f g.
End composition.

Section identity.
Context {T : topologicalType} {A : set T}.
Local Lemma cts_identity : IsContinuous _ _ A (@idfun T).
Proof. by split => x; exact: continuous_subspaceT. Qed.
HB.instance Definition _ := cts_identity.
End identity.

Section constants.
Context {T U : topologicalType} {A : set T}.
Local Lemma cts_const (y : U) : IsContinuous _ _ A (cst y).
Proof. by split => x; exact: cst_continuous. Qed.
HB.instance Definition _ (y : U) := cts_const y.
End constants.

Section affine.
Context {R : realType}.
Definition affine (a b x: R) : R := a * x + b.

Lemma affine_comp a b c d : affine a b \o affine c d = 
  affine (a * c) (a * d + b).
Proof. by apply: funext => r /=; rewrite /affine mulrDr mulrA addrA. Qed.

Lemma affine_id a : a != 0 -> affine a 0 \o affine (1/a) 0 = id.
Proof. 
move=> an0; apply: funext => r; rewrite affine_comp div1r divrr ?unitfE //. 
by rewrite /affine mulr0 ?addr0 mul1r.
Qed.

Lemma affine_ctsT (a b : R) : continuous (affine a b).
Proof. 
rewrite /affine => r; apply: cvgD; last exact: cvg_cst; exact: mulrl_continuous.
Qed.

Local Lemma cts_affine (a b : R) A : IsContinuous R R A (affine a b).
Proof. 
split => x; apply: continuous_subspaceT; exact: affine_ctsT.
Qed.

HB.instance Definition _ (a b : R) A := cts_affine a b A.

Local Lemma affine_pitv_ccE a b x y r :
  0 < a ->
  affine a b r \in `[x, y]%classic = (r \in `[(x - b)/a, (y-b)/a]%classic).
Proof.
rewrite ?in_itv /= ?ler_pdivl_mulr ?[2 * _]mulrC // ?mem_setE ?in_itv.
move: a => _/posnumP[a] /=; rewrite /affine/=.
apply: Bool.eq_true_iff_eq; split => /andP [] P Q; apply/andP; split.
- by rewrite ler_pdivr_mulr // ler_subl_addr mulrC.
- by rewrite ler_pdivl_mulr // -ler_subl_addr mulrC opprK.
- by rewrite -ler_subl_addr mulrC -ler_pdivr_mulr.
- by rewrite -[b]opprK - mulrC ler_subl_addr -ler_pdivl_mulr.
Qed.

Local Lemma affine_pitv_ocE a b x y r :
  0 < a ->
  affine a b r \in `]x, y]%classic = (r \in `](x - b)/a, (y-b)/a]%classic).
Proof.
rewrite ?in_itv /= ?ler_pdivl_mulr ?[2 * _]mulrC // ?mem_setE ?in_itv.
move: a => _/posnumP[a] /=; rewrite /affine/=.
apply: Bool.eq_true_iff_eq; split => /andP [] P Q; apply/andP; split.
- by rewrite ltr_pdivr_mulr // ltr_subl_addr mulrC.
- by rewrite ler_pdivl_mulr // -ler_subl_addr mulrC opprK.
- by rewrite -ltr_subl_addr mulrC -ltr_pdivr_mulr.
- by rewrite -[b]opprK - mulrC ler_subl_addr -ler_pdivl_mulr.
Qed.

Local Lemma affine_pmono (a b : R) : 
  0 < a -> {mono (affine a b) : x y / x <= y }.
Proof.
by move: a => _/posnumP[a] => x y; rewrite /affine  ler_add2r ler_pmul2l.
Qed.

Variables (a : {posnum R}) (b x y :R).
Local Lemma affine_fun_pitv : 
  @set_fun R R `[x,y]%classic `[a%:num*x + b, a%:num * y + b]%classic 
    (affine a%:num b).
Proof. 
move=> r /itvP rxy; rewrite /= in_itv; apply/andP.
by split => /=; rewrite /affine ler_add2r ler_wpmul2l // rxy.
Qed.

HB.instance Definition F := IsFun.Build _ _ _ _ _ affine_fun_pitv.

Definition affine_fun : {continuous `[x,y] >-> `[a%:num*x + b, a%:num * y + b]} :=
  [continuous of (affine a%:num b)].

End affine.

End continuous_hb_basics.

Section SplitDomain.
Context {R : realType}.
Implicit Types  T : topologicalType.
Let split_domain_aux {T} (f g: R -> T) := 
  (patch (g \o (affine 1 (-1))) (`[0,1]%classic) f).

Lemma split_domain_auxP {T} f g x : x \in `[0,2] -> 
  [/\ (x \in `[0, 1]) & @split_domain_aux T f g x = f x]
  \/
  [/\ x \in `]1, 2], x \in ~` `[0, 1] & @split_domain_aux T f g x = (g \o affine 1 (-1)) x].
Proof.
move=> x01; rewrite /split_domain_aux /= /patch /=.
case: ifP => xI; [left | right]; split => //; first by rewrite set_itv_set.
  rewrite in_itv /=; apply/andP; split; last by move/itvP:x01 => ->.
  rewrite real_ltNge // ?num_real //; move/negP: xI; apply: contra_notT.
  by rewrite negbK -set_itv_set in_itv /= => xh; rewrite xh (itvP x01).
by apply /mem_set => /=; rewrite set_itv_set xI.
Qed.

Lemma split_domain_aux_fun {T} B (f g : R -> T) : 
  set_fun `[0,1] B f -> set_fun `[0,1] B g -> 
  set_fun `[0,2] B (split_domain_aux f g).
Proof.
move=> funF funG x /(@split_domain_auxP T f g) [][]. 
  by move=> xI ->; first exact: funF.
move=> ? ? ->; apply: funG; rewrite /= set_itv_set affine_pitv_ccE // ?subr0 .
by rewrite opprK add0r divrr  ?unitfE // -set_itv_set divr1; apply: subset_itv_oc_cc.
Qed.

HB.instance Definition _ {T} (B : set T) {f g : {fun `[0,1] >-> B}} := 
  IsFun.Build _ _ _ _ (split_domain_aux f g) (split_domain_aux_fun funS funS).

Lemma split_cts1 {T} (f g : R -> T) : {within `[0,1], continuous f} -> 
  {within `[0,1], continuous (split_domain_aux f g)}.
Proof.
move=> ctsF; apply: (@subspace_eq_continuous _ _ _ f) => //. 
by move=> q ?; rewrite /split_domain_aux patchT.
Qed.

Lemma split_cts2 {T} (f g : R -> T) : (g 0 = f 1) -> 
  {within `[0,1], continuous g} ->
  {within `[1,2], continuous (split_domain_aux f g)}.
Proof.
move=> fg_midpoint ctsg; rewrite /split_domain_aux within_continuousE.
apply: (@subspace_eq_continuous _ _ _ (g \o (@affine_fun R (PosNum ltr01) (-1) 1 2))).
  move=> q /set_mem /=; case : (eqVneq q 1).
    move=> -> _; rewrite /patch -set_itv_set bound_itvE ler01 /affine.
    by rewrite mulr1 subrr fg_midpoint.
  move=> qn1 q12; rewrite patchC //; apply/mem_set; rewrite /= in_itv /=.
  apply/negP/nandP; right; rewrite le_eqVlt negb_or qn1 real_ltNge ?num_real //.
  by move/itvP: q12 ->.
move=> z; apply (@continuous_comp (subspace_topologicalType `[1,2]) 
    (subspace_topologicalType `[0,1]) T); last exact: ctsg.
apply: subspaceT_continuous; last apply: continuous_fun.
move=> x /(affine_fun_pitv (PosNum ltr01) (-1)); rewrite /= ?mul1r subrr.
by rewrite (_ : 2-1 = 1) // -addrA subrr addr0.
Qed.

Lemma split_domain_aux_cts {T} (f g : R -> T) : (g 0 = f 1) ->
  {within `[0,1], continuous f} ->
  {within `[0,1], continuous g} ->
  {within `[0,2], continuous (split_domain_aux f g)}.
Proof.
move=> fg_midpoint ctsf ctsg.
have : (`[0,1]%classic `|` `[1,2]%classic = `[(0:R),2]%classic).
  rewrite ?set_itvcc eqEsubset; (split => r /=; first case) => /andP [lb ub].
  - by apply/andP; split => //; apply: (ge_trans _ ub) => /=; rewrite ler_paddr.
  - by apply/andP; split => //; apply: (ge_trans lb) => /=.
  - case/orP: (@real_leVge R r (1) (num_real _) (num_real _)) => rh.
      by left; apply/andP; split.
    by right; apply/andP; split.
move=> <-; apply: withinU_continuous; (try exact: interval_closed).
  exact: split_cts1.
exact: split_cts2.
Qed.

Lemma split_domain_mono (f g : R -> R):
  f 1 <= g 0 ->
  {in `[0,1] &, {mono f : x y / x <= y}} ->
  {in `[0,1] &, {mono g : x y / x <= y}} ->
  {in `[0,2] &, {mono (split_domain_aux f g) : x y / x <= y}}.
Proof.
move=> f1g0 monof monog x y.
have fltg : forall p q, p \in `[0,1] -> q \in `]1,2] -> f p < g (affine 1 (-1) q).
  move=> p q pI qI; apply: (@le_lt_trans _ _ (f 1)). 
    by rewrite monof // ?bound_itvE // (itvP pI).
  apply: (@le_lt_trans _ _ (g 0)) => //. 
  rewrite (leW_mono_in (monog)) ?bound_itvE // ?in_itv /= /affine mul1r.
    by rewrite ltr_subr_addr add0r (itvP qI).
  by rewrite ?ler_subr_addr ?add0r ?ler_subl_addr ?(itvP qI).
move=> /(split_domain_auxP f g) [][] xI => [|?] ->; 
move=> /(split_domain_auxP f g) [][] yI => [|?] ->. 
- rewrite monof // ?affine_pmono //.
- have xley : x < y by apply (@le_lt_trans _ _ (1)); rewrite ?(itvP xI) ?(itvP yI).
  by rewrite (ltW (fltg _ _ xI yI )) // (ltW xley).
- have xley : y < x by apply (@le_lt_trans _ _ (1)); rewrite ?(itvP xI) ?(itvP yI).
  rewrite [x <= y]real_leNgt ?num_real // xley /=.
  rewrite real_leNgt ?num_real //; apply: negbF.
  rewrite fltg // (ltW xley).
- rewrite monog ?set_itv_set ?affine_pitv_ccE // ?opprK ?add0r ?divr1.
  + rewrite real_mono // ?num_real // => p q. 
    by rewrite (leW_mono (affine_pmono _ _)). 
  + by rewrite -set_itv_set; apply: subset_itv_oc_cc. 
  + by rewrite -set_itv_set; apply: subset_itv_oc_cc. 
Qed.

Definition split_domain {T} (f g: R -> T) := split_domain_aux f g \o affine 2 0.

End SplitDomain.

Section Parametrizations.
Context {R : realType}.

Lemma parametrize_monotone (f : {inj_parametrization R}) : 
  {in `[0,1] &, {mono f : x y / x <= y}}.
Proof.
apply: itv_continuous_inj_le.
- exists 0; exists 1; rewrite ?bound_itvE ?parametrize_init.
  by rewrite ?parametrize_final; split.
- apply: continuous_fun.
- by move: (@inj _ _ _ f); rewrite mem_setE.
Qed.

Section Identity.
HB.instance Definition _ := @IsParametrization.Build _ (@idfun R) erefl erefl.
Definition id_parametrization := [inj_parametrization of (@idfun R)].
End Identity. 

Section Composition.
Variables (f g : {parametrization R}).
Let h := (f \o g) : R -> R.
HB.instance Definition _ := Fun.on h.
HB.instance Definition _ := JustContinuous.on h.

Local Lemma h_init : h 0 = 0.
Proof. by rewrite /h /= ?parametrize_init. Qed.

Local Lemma h_final : h 1 = 1.
Proof. by rewrite /h /= ?parametrize_final. Qed.

HB.instance Definition _ := @IsParametrization.Build _ _ h_init h_final.

Definition comp_parametrization := [parametrization of h].

End Composition. 

Section InjComposition.
Variables (f g : {inj_parametrization R}).
Let h := (f \o g) : R -> R.
HB.instance Definition _ := SplitInjFun.on h.
HB.instance Definition _ := Parametrization.on h.

Definition comp_inj_parametrization := [inj_parametrization of h].
End InjComposition.

Section Inverses.
Local Open Scope fun_scope.
Variables (f : {inj_parametrization R}).

Let g := (f^-1) : R -> R.

Local Lemma g_continuous :IsContinuous _ _ `[0,1]%classic g.
Proof. 
split; rewrite -(@parametrize_init _ f) -(@parametrize_final _ f). 
apply: segment_can_le_continuous => //; first exact: continuous_fun.
by move=> ? ?; exact/funK/mem_set.
Qed.

HB.instance Definition _ := g_continuous.

Local Lemma g_init : g 0 = 0.
Proof. 
rewrite -[x in g x](@parametrize_init _ f) [g (f _)]funK //. 
by rewrite mem_setE /= bound_itvE.
Qed.

Local Lemma g_final : g 1 = 1.
Proof. 
rewrite -[x in g x](@parametrize_final _ f) [g (f _)]funK //. 
by rewrite mem_setE /= bound_itvE.
Qed.

Local Lemma g_cancel : {in `[0,1]%classic, cancel g f}.
Proof.
rewrite mem_setE /= -(@parametrize_init _ f) -(@parametrize_final _ f). 
apply: segment_continuous_le_can_sym => //; first exact: continuous_fun.
by move=> ? ?; apply/funK/mem_set.
Qed.

Local Lemma g_fun : set_fun `[0,1]%classic `[0,1]%classic g.
Proof.
have gle : {in `[0,1] &, {mono g : x y / x <= y}}.
  apply: itv_continuous_inj_le.
  - by exists 0; exists 1; rewrite ?bound_itvE ?g_init ?g_final; split.
  - apply: continuous_fun.
  - by apply: can_in_inj => p q; exact/g_cancel/mem_set.
move=> z; rewrite /= ?in_itv /= => /[dup] ? /andP [] ? ?.
by rewrite -g_init -g_final; apply/andP; split; rewrite gle // ?bound_itvE.
Qed.

HB.instance Definition _ := Can.Build _ _ _ g g_cancel.
HB.instance Definition _ := IsFun.Build _ _ _ _ _ g_fun.

HB.instance Definition _ := @IsParametrization.Build _ _ g_init g_final.

Definition inv_parametrization := [inj_parametrization of g].

Lemma inv_parametrization_can_r : {in `[0,1], cancel f inv_parametrization}.
Proof.
move=> z zI /=; rewrite (@segment_continuous_can_sym _ 0 1) //.
- exact: continuous_fun.
- move=> w wI; move: (@funK _ _ _ inv_parametrization w).
  by rewrite mem_setE invV => /(_ wI).
- by rewrite g_init g_final /minr /maxr ltr01.
Qed.

Lemma inv_parametrization_can_l: {in `[0,1], cancel inv_parametrization f}.
Proof.  by move=> z zI; apply: funK; rewrite mem_setE. Qed.

End Inverses.

Definition rev_param (x : R) : R := `1- x.

Local Lemma rev_param_funS : set_fun `[0,1]%classic `[0,1]%classic rev_param.
Proof.
rewrite ?set_itvcc => x /= /andP [] xnng xle1; apply/andP. 
split; [exact: onem_ge0| exact: onem_le1].
Qed.

HB.instance Definition _ := IsFun.Build R R _ _ _ rev_param_funS.

Local Lemma rev_param_continuous : {within `[0,1], continuous rev_param}. 
Proof.
move=> z; apply: continuous_subspaceT.
move=> ?; apply: (@continuousD R R R ); first exact: cvg_cst.
exact: opp_continuous.
Qed.

HB.instance Definition _ := IsContinuous.Build _ _ _ _ rev_param_continuous.

Lemma rev_param_cancel (A : set R) : {in A, cancel rev_param rev_param}.
Proof. by move=> x _; rewrite /rev_param onemK. Qed.

Lemma split_inj_rev_param : SplitInjFun _ `[0,1] `[0,1] rev_param.
Proof.
have [f /=] := funPsplitinj (@rev_param_cancel `[0,1]%classic).
rewrite (_ : rev_param = homotopy_rev_param__canonical__functions_Fun) //.
move=> ->; case: f => ?; apply.
Qed.

HB.instance Definition _ := split_inj_rev_param.

Section Reversal.
Variables (f : {parametrization R}).

Let g := rev_param \o f \o rev_param.
HB.instance Definition _ := JustContinuous.on g.
HB.instance Definition _ := Fun.on g.

Local Lemma rev_rev_init : g 0 = 0. 
Proof. by rewrite /g /= /rev_param /= onem0 parametrize_final onem1. Qed.

Local Lemma rev_rev_final : g 1 = 1. 
Proof. by rewrite /g /= /rev_param /= onem1 parametrize_init onem0. Qed.

HB.instance Definition _ := @IsParametrization.Build
  _ _ rev_rev_init rev_rev_final.

Definition double_reverse := [parametrization of g].

End Reversal.

Lemma ler12 : (1:R) <= 2.
Proof. by rewrite (_ : 1 = ((1%:R : R))) // (@ler_nat R). Qed.

Lemma ltr12 : (1:R) < 2.
Proof. by rewrite (_ : 1 = ((1%:R : R))) // (@ltr_nat R). Qed.

#[local] Hint Resolve ler12 : core.
#[local] Hint Resolve ltr12 : core.

Section InjReversal.
Variables (f : {inj_parametrization R}).
HB.instance Definition _ := Parametrization.on (double_reverse f).
HB.instance Definition _ := SplitInjFun.on (double_reverse f).

Definition double_reverse_inj := [inj_parametrization of (double_reverse f)].

End InjReversal.

Section SplitParametrization.
Context (f g: {inj_parametrization R}).
Let hpos : (0:R) < 1/2. Proof. by []. Qed.
Let pos2 : (0:R) < 2. Proof. by []. Qed.
Let shift1  := [continuous of affine_fun (PosNum hpos) 0 0 1 \o f].
Let shift2 := [continuous of affine_fun (PosNum hpos) (1/2) 0 1 \o g].

Lemma split_parametrize_fun : set_fun `[0,1] `[0,1] (split_domain shift1 shift2).
Proof.
rewrite /split_domain => x /[dup] x01 /(affine_fun_pitv (PosNum pos2) 0) /=.
rewrite mulr0 ?addr0 mulr1 => /(@split_domain_aux_fun R R `[0,1] _ _); apply.
  move=> y /(@funS _ _ _ _ shift1) /=; move: (affine _ _ _).
  rewrite mulr0 addr0; apply: subitvPr; rewrite /Order.le /= ?mulr1 addr0.
  by rewrite ler_pdivr_mulr // mul1r.
move=> y /(@funS _ _ _ _ shift2) /=; move: (affine _ _ _).
by rewrite mulr1 -splitr; apply: subitvPl; rewrite /Order.le /= ?mulr0 add0r.
Qed.

HB.instance Definition _ := @IsFun.Build _ _ _ _ _ split_parametrize_fun.

Lemma split_parametrize_cts : {within `[0,1], continuous (split_domain shift1 shift2)}.
Proof.
move=> x.
apply: (@continuous_comp (subspace_topologicalType _) (subspace_topologicalType `[0,2]) _).
  apply: subspaceT_continuous; last exact: continuous_fun.
  by move=> q /(affine_fun_pitv (PosNum pos2) 0); rewrite /= mulr0 ?addr0 mulr1.
apply: split_domain_aux_cts; last exact: continuous_fun; first last.
  exact: continuous_fun.
by rewrite /= /affine parametrize_init parametrize_final mulr0 add0r addr0 mulr1.
Qed.

HB.instance Definition _ := @IsContinuous.Build _ _ _ _ split_parametrize_cts.
 
Local Lemma split_parametrize_init : split_domain shift1 shift2 0 = 0. 
Proof. 
rewrite /split_domain /= /affine ?addr0.
by rewrite patchT mulr0 /= -?set_itv_set ?bound_itvE // addr0 parametrize_init mulr0. 
Qed.

Local Lemma split_parametrize_final : split_domain shift1 shift2 1 = 1. 
Proof. 
rewrite /split_domain /= /affine mulr1 addr0 ?mul1r patchC.
  rewrite /= mul1r (_ : 2-1 = 1); last by apply/eqP; rewrite subr_eq.
  by rewrite parametrize_final mulr1 -div1r -splitr.
rewrite in_setC; apply/negP; rewrite -set_itv_set inE=> /andP. 
rewrite /Order.le /=; apply/not_andP; right; apply/negP; rewrite -real_ltNge //.
Qed.

HB.instance Definition _ := @IsParametrization.Build _ _ 
  split_parametrize_init split_parametrize_final.

Local Lemma split_parametrize_inj : 
  @SplitInj R R `[0,1] (split_domain shift1 shift2).
Proof. 
have [] := @pPinj_ R R idfun `[0,1] (split_domain shift1 shift2); first last.
  by move=> x ->; case: x. 
apply: (mono_inj_in lexx le_anti) => x y /= /set_mem /= xI /set_mem /= yI.
rewrite split_domain_mono //; first by rewrite affine_pmono.
- by rewrite  /= parametrize_init parametrize_final /affine mulr0 addr0 add0r mulr1.
- move=> p q pI qI; rewrite /= affine_pmono //. 
  rewrite (@segment_continuous_inj_le _ _ 0 1) // ?parametrize_init ?parametrize_final //.
    exact: continuous_fun.
  move=> m n; rewrite ?set_itv_set; move: m n; exact: inj.
- move=> p q pI qI; rewrite /= affine_pmono //. 
  rewrite (@segment_continuous_inj_le _ _ 0 1) // ?parametrize_init ?parametrize_final //.
    exact: continuous_fun.
  move=> m n; rewrite ?set_itv_set; move: m n; exact: inj.
- rewrite set_itv_set affine_pitv_ccE // ?subr0 ?mul0r divrr ?unitfE //.
  by rewrite -set_itv_set.
- rewrite set_itv_set affine_pitv_ccE // ?subr0 ?mul0r divrr ?unitfE //.
  by rewrite -set_itv_set.
Qed.

HB.instance Definition _ := split_parametrize_inj.

Definition split_parametrize := [inj_parametrization of (split_domain shift1 shift2)].

End SplitParametrization.

End Parametrizations.

Section Reparametrization.

Context {R : realType} {T : topologicalType} (B : set T).

Definition reparametrize (f g : R -> T) : bool :=
  `[<exists gamma : {inj_parametrization R}, {in `[0,1], f \o gamma =1 g}>].

Lemma reflexive_reparametrize : reflexive reparametrize.
Proof. by move=> f; apply/asboolP; exists id_parametrization. Qed.

Lemma symmetric_reparametrize : symmetric reparametrize.
Proof.
by move=> f g; apply/asbool_equiv_eq; split=> [][] gamma fgamg;
    exists (inv_parametrization gamma) => z zI;
    rewrite /comp -fgamg /comp ?inv_parametrization_can_l //;
    apply: (@funS _ _ _ _ (inv_parametrization gamma)).
Qed.

Lemma transitive_reparametrize : transitive reparametrize.
Proof.
move=> f g h /asboolP [p pfg] /asboolP [q qgh]; apply/asboolP. 
exists (comp_parametrization p q) => z zI /=. 
by rewrite -qgh //= -pfg //; exact: (@funS _ _ _ _ q).
Qed.

Definition equiv_rel_reparametrize := EquivRel reparametrize 
  reflexive_reparametrize symmetric_reparametrize transitive_reparametrize.

Definition RPath := {eq_quot equiv_rel_reparametrize}.

Definition path_init := lift_fun1 RPath (fun f => f 0).

Lemma path_init_mono : {mono \pi_RPath : f / f 0 >-> path_init f}.
Proof.
move=> f; unlock path_init.
have : ((repr (\pi_(RPath) f)) = f %[mod RPath]) by rewrite reprK.
move=> /eqquotP /asboolP [] gamma /(_ 0).
by rewrite bound_itvE /= parametrize_init; exact.
Qed.

Canonical pi_path_init_mono := PiMono1 path_init_mono.

Definition path_final := lift_fun1 RPath (fun f => f 1).

Lemma path_final_mono : {mono \pi_RPath : f / f 1 >-> path_final f}.
Proof.
move=> f; unlock path_final.
have : ((repr (\pi_(RPath) f)) = f %[mod RPath]) by rewrite reprK.
move=> /eqquotP /asboolP [] gamma /(_ 1).
by rewrite bound_itvE /= parametrize_final; exact.
Qed.

Canonical pi_path_final_mono := PiMono1 path_final_mono.

Definition path_image := lift_fun1 RPath (fun f => f @` `[0,1] ).

Lemma path_image_mono : {mono \pi_RPath : f / f @` `[0,1] >-> path_image f}.
Proof.
move=> f; unlock path_image; rewrite eqEsubset; split => z /= [w wI] <-.
  have /eqquotP/asboolP [gamma fg]: f = repr (\pi_(RPath) f) %[mod RPath]. 
    by rewrite reprK.
  by (exists (gamma w); last exact: fg); exact: (@funS _ _ _ _ gamma).
have /eqquotP/asboolP [gamma fg]: repr (\pi_(RPath) f) = f %[mod RPath]. 
  by rewrite reprK.
(exists (gamma w); last exact: fg); exact: (@funS _ _ _ _ gamma).
Qed.

Canonical pi_path_image_mono := PiMono1 path_image_mono.

Let cts_fun_rev (f : R -> T) := f \o rev_param.

Definition path_reverse := lift_op1 RPath cts_fun_rev.

Lemma path_reverse_morph : {morph \pi : f / cts_fun_rev f >-> path_reverse f}.
Proof.
move=> f /=; unlock path_reverse; apply/eqquotP/asboolP. 
have /eqquotP/asboolP [gamma fg]: repr (\pi_(RPath) f) = f %[mod RPath]. 
  by rewrite reprK.
exists (double_reverse_inj (inv_parametrization gamma)) => x x01 /=.
have gx01 : (gamma^-1)%function (rev_param x) \in `[0, 1].
  apply: (@funS _ _ _ _ [fun of inv_parametrization gamma]).
  exact: funS.
rewrite /cts_fun_rev /= (@rev_param_cancel _ `[0,1]%classic) -?fg ?inE // /RPath.
  have /= := (@funK _ _ _ (inv_parametrization gamma) (rev_param x)).
by rewrite invV => -> //=; apply/mem_set; exact: funS.
Qed.

Canonical pi_path_reverse_morph := PiMorph1 path_reverse_morph.

Lemma path_reverse_final_initE (f : RPath) : 
  path_final (path_reverse f) = path_init f.
Proof.
have := path_init_mono (repr f); rewrite reprK => ->.
have := path_reverse_morph (repr f); rewrite reprK /= => <-.
rewrite (path_final_mono (cts_fun_rev (repr f))).
by rewrite /cts_fun_rev /= /rev_param onem1.
Qed.

Lemma path_reverse_init_finalE (f : RPath) : 
  path_init (path_reverse f) = path_final f.
Proof.
have := path_final_mono (repr f); rewrite reprK => ->.
have := path_reverse_morph (repr f); rewrite reprK /= => <-.
rewrite (path_init_mono (cts_fun_rev (repr f))).
by rewrite /cts_fun_rev /= /rev_param onem0.
Qed.

Lemma path_cts : {mono \pi_RPath : f / {within `[0,1], continuous f}
  >-> {within `[0,1], continuous (repr f)}}.
Proof.
move=> f; rewrite propeqE; split => ctsF.
  have /eqquotP/asboolP [gamma fpp]: repr (\pi_RPath f) = f %[mod RPath]. 
    by rewrite reprK.
  apply: subspace_eq_continuous.
    move=> x /set_mem /=; move: x; exact: fpp.
  move=> x; apply: (@continuous_comp (subspace_topologicalType _) (subspace_topologicalType `[0,1]) _).
    by apply: subspaceT_continuous; [exact: funS | exact: continuous_fun].
  exact: ctsF.
have /eqquotP/asboolP [gamma fpp]: f = repr (\pi_RPath f) %[mod RPath]. 
  by rewrite reprK.
apply: subspace_eq_continuous.
  move=> x /set_mem /=; move: x; exact: fpp.
move=> x; apply: (@continuous_comp (subspace_topologicalType _) (subspace_topologicalType _) _).
  by apply: subspaceT_continuous; [exact: funS | exact: continuous_fun].
exact: ctsF.
Qed.

Canonical pi_path_cts_mono := PiMono1 path_cts.

Definition path_link := lift_op2 RPath split_domain.

Lemma path_link_morph : {morph \pi : f g / split_domain f g >-> path_link f g}.
Proof.
move=> f g /=; unlock path_link; apply/eqquotP/asboolP. 
have /eqquotP/asboolP [r1 fpp]: (f = (repr (\pi_(RPath) f)) %[mod RPath]). 
  by rewrite reprK.
have /eqquotP/asboolP [r2 gpp]: (g = (repr (\pi_(RPath) g)) %[mod RPath]). 
  by rewrite reprK.
exists (split_parametrize r1 r2) => x x01.
have : affine 2 0 x \in `[0,2].
  by rewrite set_itv_set affine_pitv_ccE // ?subr0 mul0r divrr ?unitfE // -set_itv_set.
rewrite /split_parametrize /= /split_domain /=.
move: {x01 x} (affine 2 0 x) => x /(split_domain_auxP 
     (affine (1/2) 0 \o r1) (affine (1/2) (1/2) \o r2)) [].
  case => x01 -> /=; rewrite -/((_ 2 0 \o _ (1/2) 0) _) affine_id //.
  by rewrite ?patchT -?set_itv_set -?fpp //; last exact: (@funS _ _ _ _ r1).
case=> x12 xn01 -> /=.
rewrite -/((affine 2 0 \o affine (1/2) (1/2)) (r2 _)) affine_comp div1r divrr ?unitfE //.
rewrite addr0 {2}/affine mul1r ?patchC //=. 
  rewrite /affine ?mul1r -?addrA ?subrr ?addr0 -?gpp //= in_itv /=.
  by rewrite ler_subr_addr add0r ler_subl_addr ?(itvP x12).
have afx : affine 1 (-1) x \in `]0,1].
  by rewrite in_itv /affine /= mul1r ltr_subr_addr add0r ler_subl_addr.
have r2I : r2 (affine 1 (-1) x) \in `]0,1].
  rewrite in_itv  /= lt0r /= -andbA; apply/andP; split; first last.
    by move/subset_itv_oc_cc/(@funS _ _ _ _ r2): afx; rewrite /= in_itv.
  apply /eqP => M; suff E : x = 1. 
    by move/set_mem: xn01 => /=; rewrite E bound_itvE.
  apply: subr0_eq; apply: (@inj _ _ _ r2) => //.
  - rewrite -set_itv_set in_itv /=.
    by rewrite ler_subr_addr add0r ler_subl_addr ?(itvP x12).
  - by rewrite -set_itv_set bound_itvE.
  - rewrite parametrize_init (_ : x - 1 = affine 1 (-1) x) //. 
    by rewrite /affine mul1r.
apply/mem_set; rewrite /= in_itv /=; apply/negP/nandP; right.
by rewrite -real_ltNge ?num_real // -ltr_subl_addr subrr (itvP r2I).
Qed.

Canonical pi_path_chain_morph := PiMorph2 path_link_morph.

End Reparametrization.

HB.mixin Record IsRPathFrom {R} {T : topologicalType}
    (x : T) (f : @RPath R T) :=
  { from_point : path_init f = x }.

HB.structure Definition RPathFrom {R} {T : topologicalType}
  (x : T) := {f of @IsRPathFrom R T x f}.

HB.mixin Record IsRPathTo {R} {T : topologicalType}
    (x : T) (f : @RPath R T) :=
  { to_point : path_final f = x }.

HB.structure Definition RPathTo {R} {T : topologicalType}  
  (x : T) := {f of @IsRPathTo R T x f}.

HB.structure Definition RPathBetween {R} {T : topologicalType} 
  (x y : T) := {f of (@RPathFrom R T x f) & (@RPathTo R T y f)}.

HB.mixin Record IsPath {R} {T : topologicalType} (B : set T) (f : @RPath R T) := 
  {
    continuous_path : {within `[0,1], continuous (repr f)};
    path_fun : set_fun `[0,1]%classic B (repr f);
  }.

HB.structure Definition Path {R} {T : topologicalType} (B : set T) := 
  { f of IsPath R T B f}.

HB.structure Definition PathFrom {R} {T : topologicalType} (B : set T) (x : T) := 
  { f of IsPath R T B f & IsRPathFrom R T x f}.

HB.structure Definition PathTo {R} {T : topologicalType} (B : set T) (y : T) := 
  { f of IsPath R T B f & IsRPathTo R T y f}.

HB.structure Definition PathBetween {R} {T : topologicalType} (B : set T) (x y : T) := 
  { f of IsPath R T B f & IsRPathFrom R T x f & IsRPathTo R T y f}.

Notation "{ 'path' R 'from' x 'to' y 'in` B }" := 
  (@PathBetween.type R _ B x y) : form_scope.

Notation "{ 'Loop' R 'at' x 'in' B }" := 
  (@PathBetween.type R _ B x x) : form_scope.

Notation "[ 'loop' of' f ]" := 
  ([the (@PathBetween.type _ _ _ _ _) of (f: @Path _ _ _)]) : form_scope.
