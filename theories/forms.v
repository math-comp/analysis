From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg fingroup zmodp poly ssrnum.
From mathcomp Require Import matrix mxalgebra vector falgebra ssrnum fieldext.
From mathcomp Require Import vector mathcomp_extra.

(**md**************************************************************************)
(* # Bilinear forms                                                           *)
(* (undocumented)                                                             *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Reserved Notation "'[ u , v ]" (format "'[hv' ''[' u , '/ '  v ] ']'").
Reserved Notation "'[ u , v ]_ M" (format "'[hv' ''[' u , '/ '  v ]_ M ']'").
Reserved Notation "'[ u ]_ M" (format "''[' u ]_ M").
Reserved Notation "'[ u ]" (format "''[' u ]").
Reserved Notation "u '``_' i"
  (at level 3, i at level 2, left associativity, format "u '``_' i").
Reserved Notation "A ^_|_"    (at level 8, format "A ^_|_").
Reserved Notation "A _|_ B" (at level 69, format "A  _|_  B").
Reserved Notation "eps_theta .-sesqui" (format "eps_theta .-sesqui").

Notation "u '``_' i" := (u (0 : 'I_1) i) : ring_scope.
Notation "''e_' i" := (delta_mx 0 i)
  (at level 8, i at level 2, format "''e_' i") : ring_scope.

Local Notation "M ^ phi" := (map_mx phi M).
Local Notation "M ^t phi" := (map_mx phi (M ^T)) (phi at level 30, at level 30).

Lemma eq_map_mx_id (R : ringType) m n (M : 'M[R]_(m,n)) (f : R -> R) :
  f =1 id -> M ^ f = M.
Proof. by move=> /eq_map_mx->; rewrite map_mx_id. Qed.

HB.mixin Record isBilinear (R : ringType) (U U' : lmodType R) (V : zmodType)
    (s : R -> V -> V) (s' : R -> V -> V) (f : U -> U' -> V) := {
  additivel_subproof : forall u', additive (f^~ u');
  additiver_subproof : forall u, additive (f u);
  linearl_subproof : forall u', scalable_for s (f^~ u');
  linearr_subproof : forall u, scalable_for s' (f u);
}.

HB.structure Definition Bilinear (R : ringType) (U U' : lmodType R) (V : zmodType)
    (s : R -> V -> V) (s' : R -> V -> V) :=
  {f of isBilinear R U U' V s s' f}.

Definition bilinear_for (R : ringType) (U U' : lmodType R) (V : zmodType)
    (s : GRing.Scale.law R V) (s' : GRing.Scale.law R V) (f : U -> U' -> V) :=
  ((forall u', GRing.linear_for (s : R -> V -> V) (f^~ u'))
  * (forall u, GRing.linear_for s' (f u)))%type.

HB.factory Record bilinear_isBilinear (R : ringType) (U U' : lmodType R) (V : zmodType)
    (s : GRing.Scale.law R V) (s' : GRing.Scale.law R V) (f : U -> U' -> V) := {
  bilinear_subproof : bilinear_for s s' f;
}.

HB.builders Context R U U' V s s' f of bilinear_isBilinear R U U' V s s' f.
HB.instance Definition _ := isBilinear.Build R U U' V s s' f
    (fun u' => additive_linear (bilinear_subproof.1 u'))
    (fun u => additive_linear (bilinear_subproof.2 u))
    (fun u' => scalable_linear (bilinear_subproof.1 u'))
    (fun u => scalable_linear (bilinear_subproof.2 u)).
HB.end.

Module BilinearExports.
Notation bilinear f := (bilinear_for *:%R *:%R f).
Notation biscalar f := (bilinear_for *%R *%R f).
Module Bilinear.
Definition map (R : ringType) (U U' : lmodType R) (V : zmodType)
    (s : R -> V -> V) (s' : R -> V -> V)
    (phUU'V : phant (U -> U' -> V)) := Bilinear.type U U' s s'.
End Bilinear.
Notation "{ 'bilinear' fUV | s & s' }" := (Bilinear.map s s' (Phant fUV))
  (at level 0, format "{ 'bilinear'  fUV  |  s  &  s' }") : ring_scope.
Notation "{ 'bilinear' fUV | s }" := (Bilinear.map s.1 s.2 (Phant fUV))
  (at level 0, format "{ 'bilinear'  fUV  |  s }") : ring_scope.
Notation "{ 'bilinear' fUV }" := {bilinear fUV | *:%R & *:%R}
  (at level 0, format "{ 'bilinear'  fUV }") : ring_scope.
Notation "{ 'biscalar' U }" := {bilinear U -> U -> _ | *%R & *%R}
  (at level 0, format "{ 'biscalar'  U }") : ring_scope.
Notation "[ 'bilinear' 'of' f 'as' g ]" := (Bilinear.clone _ _ _ _ _ _ f g)
  (at level 0, format "[ 'bilinear'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'bilinear' 'of' f ]" := (Bilinear.clone _ _ _ _ _ _ f _)
  (at level 0, format "[ 'bilinear'  'of'  f ]") : form_scope.
End BilinearExports.
Export BilinearExports.

Section applyr.

Variables (R : ringType) (U U' : lmodType R) (V : zmodType) (s s' : R -> V -> V).

(* Fact applyr_key : unit. Proof. exact. Qed. *)
Definition applyr_head t (f : U -> U' -> V) u v := let: tt := t in f v u.

End applyr.

Notation applyr := (applyr_head tt).

Section BilinearTheory.

Variable R : ringType.

Section GenericProperties.

Variables (U U' : lmodType R) (V : zmodType) (s : R -> V -> V) (s' : R -> V -> V).
Variable f : {bilinear U -> U' -> V | s & s'}.

Section GenericPropertiesr.

Variable z : U.

#[local, non_forgetful_inheritance]
HB.instance Definition _ :=
  GRing.isAdditive.Build _ _ (f z) (@additiver_subproof _ _ _ _ _ _ f z).
#[local, non_forgetful_inheritance]
HB.instance Definition _ :=
  GRing.isScalable.Build _ _ _ _ (f z) (@linearr_subproof _ _ _ _ _ _ f z).

Lemma linear0r : f z 0 = 0. Proof. by rewrite raddf0. Qed.
Lemma linearNr : {morph f z : x / - x}. Proof. exact: raddfN. Qed.
Lemma linearDr : {morph f z : x y / x + y}. Proof. exact: raddfD. Qed.
Lemma linearBr : {morph f z : x y / x - y}. Proof. exact: raddfB. Qed.
Lemma linearMnr n : {morph f z : x / x *+ n}. Proof. exact: raddfMn. Qed.
Lemma linearMNnr n : {morph f z : x / x *- n}. Proof. exact: raddfMNn. Qed.
Lemma linear_sumr I r (P : pred I) E :
  f z (\sum_(i <- r | P i) E i) = \sum_(i <- r | P i) f z (E i).
Proof. exact: raddf_sum. Qed.

Lemma linearZr_LR : scalable_for s' (f z). Proof. exact: linearZ_LR. Qed.
Lemma linearPr a : {morph f z : u v / a *: u + v >-> s' a u + v}.
Proof. exact: linearP. Qed.

End GenericPropertiesr.

Lemma applyrE x : applyr f x =1 f^~ x. Proof. by []. Qed.

Section GenericPropertiesl.

Variable z : U'.

#[local, non_forgetful_inheritance]
HB.instance Definition _ :=
  GRing.isAdditive.Build _ _ (applyr f z) (@additivel_subproof _ _ _ _ _ _ f z).
#[local, non_forgetful_inheritance]
HB.instance Definition _ :=
  GRing.isScalable.Build _ _ _ _ (applyr f z) (@linearl_subproof _ _ _ _ _ _ f z).

Lemma linear0l : f 0 z = 0. Proof. by rewrite -applyrE raddf0. Qed.
Lemma linearNl : {morph f^~ z : x / - x}.
Proof. by move=> ?; rewrite -applyrE raddfN. Qed.
Lemma linearDl : {morph f^~ z : x y / x + y}.
Proof. by move=> ??; rewrite -applyrE raddfD. Qed.
Lemma linearBl : {morph f^~ z : x y / x - y}.
Proof. by move=> ??; rewrite -applyrE raddfB. Qed.
Lemma linearMnl n : {morph f^~ z : x / x *+ n}.
Proof. by move=> ?; rewrite -applyrE raddfMn. Qed.
Lemma linearMNnl n : {morph f^~ z : x / x *- n}.
Proof. by move=> ?; rewrite -applyrE raddfMNn. Qed.
Lemma linear_suml I r (P : pred I) E :
  f (\sum_(i <- r | P i) E i) z = \sum_(i <- r | P i) f (E i) z.
Proof. by rewrite -applyrE raddf_sum. Qed.

Lemma linearZl_LR : scalable_for s (f^~ z).
Proof. by move=> ??; rewrite -applyrE linearZ_LR. Qed.
Lemma linearPl a : {morph f^~ z : u v / a *: u + v >-> s a u + v}.
Proof. by move=> ??; rewrite -applyrE linearP. Qed.

End GenericPropertiesl.

End GenericProperties.

Section BidirectionalLinearZ.

Variables (U : lmodType R) (V : zmodType) (s : R -> V -> V).
Variables (S : ringType) (h : GRing.Scale.law S V).

(* Lemma linearZr z c a (h_c := GRing.Scale.op h_law c) (f : GRing.Linear.map_for U s a h_c) u : *)
(*   f z (a *: u) = h_c (GRing.Linear.wrap (f z) u). *)
(* Proof. by rewrite linearZ_LR; case: f => f /= ->. Qed. *)

End BidirectionalLinearZ.

End BilinearTheory.

Lemma mulmx_is_bilinear (R : comRingType) m n p :
  bilinear_for
    (GRing.Scale.Law.clone _ _ *:%R _) (GRing.Scale.Law.clone _ _ *:%R _)
    (@mulmx R m n p).
Proof.
split=> [u'|u] a x y /=.
- by rewrite mulmxDl scalemxAl.
- by rewrite mulmxDr scalemxAr.
Qed.

HB.instance Definition _ (R : comRingType) m n p :=
  bilinear_isBilinear.Build R
    'M[R]_(m, n) 'M[R]_(n, p) 'M[R]_(m, p) _ _ (@mulmx R m n p)
    (mulmx_is_bilinear R m n p).

(* Section classfun. *)
(* Import mathcomp.character.classfun. *)

(* Canonical rev_cfdot (gT : finGroupType) (B : {set gT}) :=  *)
(*   @RevOp _ _ _ (@cfdotr_head gT B tt) *)
(*   (@cfdot gT B) (fun _ _ => erefl). *)

(* Section Cfdot. *)
(* Variables (gT : finGroupType) (G : {group gT}). *)
(* Lemma cfdot_is_linear xi : linear_for (@conjC _ \; *%R) (cfdot xi : 'CF(G) -> algC^o). *)
(* Proof. *)
(* move=> /= a phi psi; rewrite cfdotC -cfdotrE linearD linearZ /=. *)
(* by rewrite !['[_, xi]]cfdotC rmorphD rmorphM !conjCK. *)
(* Qed. *)
(* Canonical cfdot_additive xi := Additive (cfdot_is_linear xi). *)
(* Canonical cfdot_linear xi := Linear (cfdot_is_linear xi). *)
(* End Cfdot. *)

(* Canonical cfdot_bilinear (gT : finGroupType) (B : {group gT}) := *)
(*   [bilinear of @cfdot gT B]. *)
(* End classfun. *)

Section BilinearForms.

Variables (R : fieldType) (theta : {rmorphism R -> R}).
Variables (n : nat) (M : 'M[R]_n).
Implicit Types (a b : R) (u v : 'rV[R]_n) (N P Q : 'M[R]_n).

Definition form u v := (u *m M *m (v ^t theta)) 0 0.

Local Notation "''[' u , v ]" := (form u%R v%R) : ring_scope.
Local Notation "''[' u ]" := '[u, u] : ring_scope.

Lemma form0l u : '[0, u] = 0.
Proof. by rewrite /form !mul0mx mxE. Qed.

Lemma form0r u : '[u, 0] = 0.
Proof. by rewrite /form trmx0 map_mx0 mulmx0 mxE. Qed.

Lemma formDl u v w : '[u + v, w] = '[u, w] + '[v, w].
Proof. by rewrite /form !mulmxDl mxE. Qed.

Lemma formDr u v w : '[u, v + w] = '[u, v] + '[u, w].
Proof. by rewrite /form linearD !map_mxD !mulmxDr mxE. Qed.

Lemma formZr a u v : '[u, a *: v] = theta a * '[u, v].
Proof. by rewrite /form !(linearZ, map_mxZ) /= mxE. Qed.

Lemma formZl a u v : '[a *: u, v] = a * '[u, v].
Proof.
by do !rewrite /form  -[_ *: _ *m _]/(mulmxr _ _) linearZ /=; rewrite mxE.
Qed.

Lemma formNl u v : '[- u, v] = - '[u, v].
Proof. by rewrite -scaleN1r formZl mulN1r. Qed.

Lemma formNr u v : '[u, - v] = - '[u, v].
Proof. by rewrite -scaleN1r formZr rmorphN1 mulN1r. Qed.

Lemma formee i j : '['e_i, 'e_j] = M i j.
Proof.
rewrite /form -rowE -map_trmx map_delta_mx -[M in LHS]trmxK.
by rewrite -tr_col -trmx_mul -rowE !mxE.
Qed.

Lemma form0_eq0 : M = 0 -> forall u v, '[u, v] = 0.
Proof. by rewrite/form=> -> u v; rewrite mulmx0 mul0mx mxE. Qed.

End BilinearForms.

Section Sesquilinear.

Variable R : fieldType.
Variable n : nat.
Implicit Types (a b : R) (u v : 'rV[R]_n) (N P Q : 'M[R]_n).

Section Def.
Variable eps_theta : (bool * {rmorphism R -> R}).

Definition sesqui :=
  [qualify M : 'M_n | M == ((-1) ^+ eps_theta.1) *: M ^t eps_theta.2].
Fact sesqui_key : pred_key sesqui. Proof. by []. Qed.
Canonical sesqui_keyed := KeyedQualifier sesqui_key.
End Def.

Local Notation "eps_theta .-sesqui" := (sesqui eps_theta).

Variables (eps : bool) (theta : {rmorphism R -> R}).
Variables (M : 'M[R]_n).
Local Notation "''[' u , v ]" := (form theta M u%R v%R) : ring_scope.
Local Notation "''[' u ]" := '[u, u] : ring_scope.

Lemma sesquiE : (M \is (eps,theta).-sesqui) = (M == (-1) ^+ eps *: M ^t theta).
Proof. by rewrite qualifE. Qed.

Lemma sesquiP : reflect (M = (-1) ^+ eps *: M ^t theta)
                        (M \is (eps,theta).-sesqui).
Proof. by rewrite sesquiE; apply/eqP. Qed.

Hypothesis (thetaK : involutive theta).
Hypothesis (M_sesqui : M \is (eps, theta).-sesqui).

Lemma trmx_sesqui : M^T = (-1) ^+ eps *: M ^ theta.
Proof.
rewrite [in LHS](sesquiP _) // -mul_scalar_mx trmx_mul.
by rewrite tr_scalar_mx mul_mx_scalar map_trmx trmxK.
Qed.

Lemma maptrmx_sesqui : M^t theta = (-1) ^+ eps *: M.
Proof.
by rewrite trmx_sesqui map_mxZ rmorph_sign -map_mx_comp eq_map_mx_id.
Qed.

Lemma formC u v : '[u, v] = (-1) ^+ eps * theta '[v, u].
Proof.
rewrite /form [M in LHS](sesquiP _) // -mulmxA !mxE rmorph_sum mulr_sumr.
apply: eq_bigr => /= i _; rewrite !(mxE, mulr_sumr, mulr_suml, rmorph_sum).
apply: eq_bigr => /= j _; rewrite !mxE !rmorphM  mulrCA -!mulrA.
by congr (_ * _); rewrite mulrA mulrC /= thetaK.
Qed.

Lemma form_eq0C u v : ('[u, v] == 0) = ('[v, u] == 0).
Proof. by rewrite formC mulf_eq0 signr_eq0 /= fmorph_eq0. Qed.

Definition ortho m (B : 'M_(m,n)) := (kermx (M *m (B ^t theta))).
Local Notation "B ^_|_" := (ortho B) : ring_scope.
Local Notation "A _|_ B" := (A%MS <= B^_|_)%MS : ring_scope.

Lemma normalE u v : (u _|_ v) = ('[u, v] == 0).
Proof.
by rewrite (sameP sub_kermxP eqP) mulmxA [_ *m _^t _]mx11_scalar fmorph_eq0.
Qed.

Lemma form_eq0P {u v} : reflect ('[u, v] = 0) (u _|_ v).
Proof. by rewrite normalE; apply/eqP. Qed.

Lemma normalP p q (A : 'M_(p, n)) (B :'M_(q, n)) :
  reflect (forall (u v : 'rV_n), (u <= A)%MS -> (v <= B)%MS -> u _|_ v)
          (A _|_ B).
Proof.
apply: (iffP idP) => AnB.
  move=> u v uA vB; rewrite (submx_trans uA) // (submx_trans AnB) //.
  apply/sub_kermxP; have /submxP [w ->] := vB.
  rewrite trmx_mul map_mxM !mulmxA -[kermx _ *m _ *m _]mulmxA.
  by rewrite [kermx _ *m _](sub_kermxP _) // mul0mx.
apply/rV_subP => u /AnB /(_ _) /sub_kermxP uMv; apply/sub_kermxP.
suff: forall m (v : 'rV[R]_m),
  (forall i, v *m 'e_i ^t theta = 0 :> 'M_1) -> v = 0.
  apply => i; rewrite !mulmxA -!mulmxA -map_mxM -trmx_mul uMv //.
  by apply/submxP; exists 'e_i.
move=> /= m v Hv; apply: (can_inj (@trmxK _ _ _)).
rewrite trmx0; apply/row_matrixP=> i; rewrite row0 rowE.
apply: (can_inj (@trmxK _ _ _)); rewrite trmx0 trmx_mul trmxK.
by rewrite -(map_delta_mx theta) map_trmx Hv.
Qed.

Lemma normalC p q (A : 'M_(p, n)) (B :'M_(q, n)) : (A _|_ B) = (B _|_ A).
Proof.
gen have nC : p q A B / A _|_ B -> B _|_ A; last by apply/idP/idP; apply/nC.
move=> AnB; apply/normalP => u v ? ?; rewrite normalE.
rewrite formC mulf_eq0 ?fmorph_eq0 ?signr_eq0 /=.
by rewrite -normalE (normalP _ _ AnB).
Qed.

Lemma normal_ortho_mx p (A : 'M_(p, n)) : ((A^_|_) _|_ A).
Proof. by []. Qed.

Lemma normal_mx_ortho p (A : 'M_(p, n)) : (A _|_ (A^_|_)).
Proof. by rewrite normalC. Qed.

Lemma rank_normal u : (\rank (u ^_|_) >= n.-1)%N.
Proof.
rewrite mxrank_ker -subn1 leq_sub2l //.
by rewrite (leq_trans (mxrankM_maxr  _ _)) // rank_leq_col.
Qed.

Definition rad := 1%:M^_|_.

Lemma rad_ker : rad = kermx M.
Proof. by rewrite /rad /ortho trmx1 map_mx1 mulmx1. Qed.

(* Pythagore *)
Theorem formDd u v : u _|_ v -> '[u + v] = '[u] + '[v].
Proof.
move=> uNv; rewrite formDl !formDr ['[v, u]]formC.
by rewrite ['[u, v]](form_eq0P _) // rmorph0 mulr0 addr0 add0r.
Qed.

Lemma formZ a u : '[a *: u]= (a * theta a) * '[u].
Proof. by rewrite formZl formZr mulrA. Qed.

Lemma formN u : '[- u] = '[u].
Proof. by rewrite formNr formNl opprK. Qed.

Lemma form_sign m u : '[(-1) ^+ m *: u] = '[u].
Proof. by rewrite -signr_odd scaler_sign; case: odd; rewrite ?formN. Qed.

Lemma formD u v : let d := '[u, v] in
  '[u + v] = '[u] + '[v] + (d + (-1) ^+ eps * theta d).
Proof. by rewrite formDl !formDr ['[v, _]]formC [_ + '[v]]addrC addrACA. Qed.

Lemma formB u v : let d := '[u, v] in
  '[u - v] = '[u] + '[v] - (d + (-1) ^+ eps * theta d).
Proof. by rewrite formD formN !formNr rmorphN mulrN -opprD. Qed.

Lemma formBd u v : u _|_ v -> '[u - v] = '[u] + '[v].
Proof.
by move=> uTv; rewrite formDd ?formN // normalE formNr oppr_eq0 -normalE.
Qed.

(* Lemma formJ u v : '[u ^ theta, v ^ theta] = (-1) ^+ eps * theta '[u, v]. *)
(* Proof. *)
(* rewrite {1}/form -map_trmx -map_mx_comp (@eq_map_mx _ _ _ _ _ id) ?map_mx_id //. *)
(* set x := (_ *m _); have -> : x 0 0 = theta ((x^t theta) 0 0) by rewrite !mxE. *)
(* rewrite !trmx_mul trmxK map_trmx mulmxA !map_mxM. *)
(* rewrite maptrmx_sesqui -!scalemxAr -scalemxAl mxE rmorphM rmorph_sign. *)

(* Lemma formJ u : '[u ^ theta] = (-1) ^+ eps * '[u]. *)
(* Proof.  *)
(* rewrite {1}/form -map_trmx -map_mx_comp (@eq_map_mx _ _ _ _ _ id) ?map_mx_id //. *)
(* set x := (_ *m _); have -> : x 0 0 = theta ((x^t theta) 0 0) by rewrite !mxE. *)
(* rewrite !trmx_mul trmxK map_trmx mulmxA !map_mxM. *)
(* rewrite maptrmx_sesqui -!scalemxAr -scalemxAl mxE rmorphM rmorph_sign. *)
(* rewrite !map_mxM. *)
(* rewrite -map_mx_comp eq_map_mx_id //. *)
(*  !linearZr_LR /=. linearZ. *)
(*  linearZl. *)
(* rewrite trmx_sesqui. *)


(* rewrite mapmx. *)
(* rewrite map *)
(* apply/matrixP.  *)

(* rewrite formC. *)
(* Proof. by rewrite cfdot_conjC geC0_conj // cfnorm_ge0. Qed. *)

(* Lemma cfCauchySchwarz u v : *)
(*   `|'[u, v]| ^+ 2 <= '[u] * '[v] ?= iff ~~ free (u :: v). *)
(* Proof. *)
(* rewrite free_cons span_seq1 seq1_free -negb_or negbK orbC. *)
(* have [-> | nz_v] /= := altP (v =P 0). *)
(*   by apply/lerifP; rewrite !cfdot0r normCK mul0r mulr0. *)
(* without loss ou: u / '[u, v] = 0. *)
(*   move=> IHo; pose a := '[u, v] / '[v]; pose u1 := u - a *: v. *)
(*   have ou: '[u1, v] = 0. *)
(*     by rewrite cfdotBl cfdotZl divfK ?cfnorm_eq0 ?subrr. *)
(*   rewrite (canRL (subrK _) (erefl u1)) rpredDr ?rpredZ ?memv_line //. *)
(*   rewrite cfdotDl ou add0r cfdotZl normrM (ger0_norm (cfnorm_ge0 _)). *)
(*   rewrite exprMn mulrA -cfnormZ cfnormDd; last by rewrite cfdotZr ou mulr0. *)
(*   by have:= IHo _ ou; rewrite mulrDl -lerif_subLR subrr ou normCK mul0r. *)
(* rewrite ou normCK mul0r; split; first by rewrite mulr_ge0 ?cfnorm_ge0. *)
(* rewrite eq_sym mulf_eq0 orbC cfnorm_eq0 (negPf nz_v) /=. *)
(* apply/idP/idP=> [|/vlineP[a {2}->]]; last by rewrite cfdotZr ou mulr0. *)
(* by rewrite cfnorm_eq0 => /eqP->; apply: rpred0. *)
(* Qed. *)

End Sesquilinear.

Notation "eps_theta .-sesqui" := (sesqui _ eps_theta) : ring_scope.

Notation symmetric_form := (false, idfun).-sesqui.
Notation skew := (true, idfun).-sesqui.
Notation hermitian := (false, @Num.conj_op _).-sesqui.

(* Section ClassificationForm. *)

(* Variables (F : fieldType) (L : fieldExtType) (theat : 'Aut()) *)

(* Notation "''[' u , v ]_ M" := (form M%R u%R v%R) : ring_scope. *)
(* Notation "''[' u ]_ M" := (form M%R u%R u%R) : ring_scope. *)

(* Hypothesis (thetaK : involutive theta). *)

(* Lemma sesqui_test M : (forall u v, '[v, u]_M = 0 -> '[u, v]_M = 0) -> *)
(*                       {eps | eps^+2 = 1 & M \is (eps,theta).-sesqui}. *)
(* Proof. *)
(* pose  *)


(*                       [/\ forall u, '[u] = 0, theta =1 id & eps = -1] *)
(*                       \/ ((exists u, '[u] != 0) /\ (eps = 1)). *)
(* Proof. *)
(* move=> M_neq0 form_eq0. *)
(* have [] := boolP [forall i : 'I_n, '['e_i] == 0]; last first. *)
(*   rewrite negb_forall => /existsP [i ei_neq0]. *)
(*   right; split; first by exists ('e_i). *)
(*   apply/eqP; *)

(*  contraT *)


(* suff [f_eq0|] : (forall u, '[u] = 0) \/ (exists u, '[u] != 0). *)
(*   left; split=> //. *)

(* have [] := boolP [forall i : 'I_n, '['e_i] == 0]. *)

(* suff /eqP : eps ^+ 2 = 1. *)
(*   rewrite -subr_eq0 subr_sqr_1 mulf_eq0. *)
(*   move => /orP[]; rewrite addr_eq0 ?opprK=> /eqP eps_eq. *)
(*     right; split=> //. *)

(* have [] := boolP [forall i : 'I_n, '['e_i] == 0]. *)

(* have := sesquiC u u. *)


(* rewrite !linearZ /= -[eps *: _ *m _]/(mulmxr _ _) linearZ /= mxE; congr (_ * _). *)
(* have : u = map_mx theta (map_mx theta u). *)
(*   apply/rowP=> i; rewrite !mxE. *)
(* rewrite -[in LHS]mulmxA -map_mxM. *)
(* rewrite  *)
(*  !mxE rmorph_sum; apply: eq_bigr => /= i _; rewrite !mxE. *)
(* rewrite !rmorphM thetaK rmorph_sum. *)

(* Hypothesis (M_sesqui : M \is (eps, theta).-sesqui). *)

(* rewrite -[a *: u *m _]/(mulmxr _ _). *)
(* rewrite linearZ. *)

(* Variables (R : fieldType) (n : nat). *)

(* Local Notation "A _|_ B" := (A%MS <= kermx B%MS^T)%MS. *)

(* Lemma normal_sym k m (A : 'M[R]_(k,n)) (B : 'M[R]_(m,n)) : *)
(*   A _|_ B = B _|_ A. *)
(* Proof. *)
(* rewrite !(sameP sub_kermxP eqP) -{1}[A]trmxK -trmx_mul. *)
(* by rewrite -{1}trmx0 (inj_eq (@trmx_inj _ _ _)). *)
(* Qed. *)

(* Lemma normalNm k m (A : 'M[R]_(k,n)) (B : 'M[R]_(m,n)) : (- A) _|_ B = A _|_ B. *)
(* Proof. by rewrite eqmx_opp. Qed. *)

(* Lemma normalmN k m (A : 'M[R]_(k,n)) (B : 'M[R]_(m,n)) : A _|_ (- B) = A _|_ B. *)
(* Proof. by rewrite ![A _|_ _]normal_sym normalNm. Qed. *)

(* Lemma normalDm k m p (A : 'M[R]_(k,n)) (B : 'M[R]_(m,n)) (C : 'M[R]_(p,n)) : *)
(*   (A + B _|_ C) = (A _|_ C) && (B _|_ C). *)
(* Proof. by rewrite addsmxE !(sameP sub_kermxP eqP) mul_col_mx col_mx_eq0. Qed. *)

(* Lemma normalmD  k m p (A : 'M[R]_(k,n)) (B : 'M[R]_(m,n)) (C : 'M[R]_(p,n)) : *)
(*   (A _|_ B + C) = (A _|_ B) && (A _|_ C). *)
(* Proof. by rewrite ![A _|_ _]normal_sym normalDm. Qed. *)

(* Definition dot (u v : 'rV[R]_n) : R := (u *m v^T) 0 0. *)

(* Notation "''[' u , v ]" := (dot u v) : ring_scope. *)
(* Notation "''[' u ]" := '[u, u]%MS : ring_scope. *)

(* Lemma dotmulE (u v : 'rV[R]_n) : '[u, v] = \sum_k u``_k * v``_k. *)
(* Proof. by rewrite [LHS]mxE; apply: eq_bigr=> i; rewrite mxE. Qed. *)

(* Lemma normalvv (u v : 'rV[R]_n) : (u _|_ v) = ('[u, v] == 0). *)
(* Proof. by rewrite (sameP sub_kermxP eqP) [_ *m _^T]mx11_scalar fmorph_eq0. Qed. *)

(* End Normal. *)

(* Local Notation "''[' u , v ]" := (form u v) : ring_scope. *)
(* Local Notation "''[' u ]" := '[u%R, u%R] : ring_scope. *)
(* Local Notation "A _|_ B" := (A%MS <= kermx B%MS^T)%MS. *)
