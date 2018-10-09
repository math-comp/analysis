(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
Require Import Reals.
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssrnat eqtype choice fintype bigop ssralg ssrnum.
Require Import boolp reals.
Require Import classical_sets posnum topology hierarchy landau derive Rstruct.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Def Num.Theory.

Lemma continuity_pt_locally f x : continuity_pt f x <->
  forall eps : {posnum R}, locally x (fun u => `|f u - f x| < eps%:num).
Proof.
split=> [fcont e|fcont _/RltP/posnumP[e]]; last first.
  have /locally_normP [_/posnumP[d] xd_fxe] := fcont e.
  exists d%:num; split; first by apply/RltP; have := [gt0 of d%:num].
  by move=> y [_ /RltP yxd]; apply/RltP/xd_fxe; rewrite /= normmB.
apply/locally_normP; have /RltP egt0 := [gt0 of e%:num].
have [_ [/RltP/posnumP[d] dx_fxe]] := fcont e%:num egt0.
exists d%:num => // y xyd; case: (eqVneq x y) => [->|xney].
  by rewrite subrr normr0.
apply/RltP/dx_fxe; split; first by split=> //; apply/eqP.
by have /RltP := xyd; rewrite normmB.
Qed.

Local Open Scope classical_set_scope.

Lemma continuity_pt_flim (f : R -> R) (x : R) :
  continuity_pt f x <-> {for x, continuous f}.
Proof.
apply: iff_trans (continuity_pt_locally _ _) _; apply: iff_sym.
have FF : Filter (f @ x).
(* (* BUG: this should work *) *)
(*   by typeclasses eauto. *)
  by apply filtermap_filter; apply: @filter_filter' (locally_filter _).
apply: iff_trans (flim_normP (f x)) _; split=> [fx e|fx _/posnumP[e]].
  have /fx := [gt0 of e%:num].
  by rewrite !near_simpl; apply: filter_app; near=> y; rewrite distrC.
have := fx e; rewrite !near_simpl; apply: filter_app.
by near=> y; rewrite distrC.
Unshelve. all: end_near. Qed.

Lemma continuity_ptE (f : R -> R) (x : R) :
  continuity_pt f x <-> {for x, continuous f}.
Proof. exact: continuity_pt_flim. Qed.

Lemma continuity_pt_flim' f x :
  continuity_pt f x <-> f @ locally' x --> f x.
Proof. by rewrite continuity_ptE continuous_withinNx. Qed.

Lemma continuity_pt_locally' f x :
  continuity_pt f x <->
  forall eps : R, 0 < eps -> locally' x (fun u => `|f x - f u| < eps)%R.
Proof.
by rewrite continuity_pt_flim' (@flim_normP _ [normedModType R of R^o]).
Qed.

Lemma locally_pt_comp (P : R -> Prop) (f : R -> R) (x : R) :
  locally (f x) P -> continuity_pt f x -> \near x, P (f x).
Proof. by move=> Lf /continuity_pt_flim; apply. Qed.

Lemma is_derive_Reals (f : R^o -> R^o) (x l : R) :
  is_derive x 1 f l <-> derivable_pt_lim f x l.
Proof.
split=> f'l.
  move=> _/RltP/posnumP[e].
  have /ex_derive/derivable_locallyP/eqaddoP/(_ _ [gt0 of e%:num / 2]) := f'l.
  rewrite near_simpl -locally_nearE -filter_from_norm_locally.
  move=> [d /RltP lt0d dfE]; exists (mkposreal _ lt0d) => h /eqP hn0 /RltP hd.
  apply/RltP; have /= := dfE h; rewrite normmB subr0 => /(_ hd).
  rewrite -[(_ - _ : _ -> _) _]/(_ - _) -[(_ + _ : _ -> _) _]/(_ + _) /cst.
  rewrite derive_val opprD addrA -ler_pdivr_mulr ?normm_gt0 //.
  rewrite mulrC -normfV -normmZ scalerBr scalerA mulVf // scale1r [_ *: _]mulrC.
  rewrite [X in f (X + _)]mulr1 RminusE RdivE // RminusE RplusE [h + _]addrC.
  by move=> /ler_lt_trans; apply; rewrite [X in _ < X]splitr ltr_addl.
have {f'l} f'l :
  (fun h => h^-1 *: ((f (h + x) - f x))) @ locally' (0 : R) --> l.
  move=> A /= /locally_normP [_/posnumP[e] sA]; apply/locally_normP.
  have /RltP /f'l [[/= _/RltP/posnumP[d] df]] := [gt0 of e%:num].
  exists d%:num => // h /=; rewrite normmB subr0 => /RltP hd hn0.
  have /eqP /df /(_ hd) /RltP := hn0.
  rewrite RminusE RdivE // RminusE RplusE => dfx.
  by apply: sA; rewrite /= normmB [_ *: _]mulrC [h + _]addrC.
have /flim_lim dfE := f'l; apply: DeriveDef; last by rewrite -derive1E .
apply/eqolimP/eqaddoP => _/posnumP[e]; near=> h => /=.
have -> : (fun h => h^-1 *: (f (h%:A + (x : R^o)) - f x)) =
  (fun h => h^-1 *: (f (h + x) - f x)).
  by rewrite funeqE => ?; rewrite [X in f (X + _)]mulr1.
rewrite -[(_ - _ : _ -> _) _]/(_ - _) {1}/cst /=.
have /eqolimP := f'l; rewrite funeqE => /(_ h) ->.
by rewrite dfE addrC addKr; near: h; case: e => /=; apply: littleoP.
Grab Existential Variables. end_near. Qed.

Lemma derivable_Reals (f : R -> R) (x : R) :
  derivable f x 1 -> derivable_pt f x.
Proof. by move=> /derivableP /is_derive_Reals; exists ('D_1 f x). Qed.

Lemma Reals_derivable (f : R -> R) (x : R) :
  derivable_pt f x -> derivable f x 1.
Proof. by move=> [l /is_derive_Reals]; apply: ex_derive. Qed.

Lemma derive1_Reals (f : R -> R) (x : R) (pr : derivable_pt f x) :
  derive_pt f x pr = f^`() x.
Proof.
by case: pr => /= l /is_derive_Reals /derive_val <-; rewrite derive1E.
Qed.
