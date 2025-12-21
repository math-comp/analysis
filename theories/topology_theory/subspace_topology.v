(* mathcomp analysis (c) 2025 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import topology_structure uniform_structure compact .
From mathcomp Require Import pseudometric_structure connected weak_topology.
From mathcomp Require Import product_topology.

(**md**************************************************************************)
(* # Subspaces of topological spaces                                          *)
(*                                                                            *)
(* ```                                                                        *)
(*               subspace A == for (A : set T), this is a copy of T with a    *)
(*                             topology that ignores points outside A         *)
(*          incl_subspace x == with x of type subspace A with (A : set T),    *)
(*                             inclusion of subspace A into T                 *)
(*          nbhs_subspace x == filter associated with x : subspace A          *)
(*        from_subspace A f == function of type `subspace A -> U` given a     *)
(*                             function f of type `A -> U`                    *)
(*                             The purpose of this definition is to preserve  *)
(*                             the pretty-printing of the notation            *)
(*                             {within _, continuous _} below. Its use is     *)
(*                             however likely to be later superseded by a     *)
(*                             better (compositional) mechanism.              *)
(* {within A, continuous f} := continuous (from_subspace A f))                *)
(*           subspace_ent A == subspace entourages                            *)
(*          subspace_ball A == balls of the pseudometric subspace structure   *)
(*    continuousFunType A B == type of continuous functions from set A to     *)
(*                             set B with domain subspace A                   *)
(*                             The HB structure is ContinuousFun.             *)
(* ```                                                                        *)
(******************************************************************************)

Reserved Notation "{ 'within' A , 'continuous' f }"
  (format "{ 'within'  A ,  'continuous'  f }").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Definition subspace {T : Type} (A : set T) := T.
Arguments subspace {T} _ : simpl never.

Definition incl_subspace {T A} (x : subspace A) : T := x.

Section Subspace.
Context {T : topologicalType} (A : set T).
Definition nbhs_subspace (x : subspace A) : set_system (subspace A) :=
  if x \in A then within A (nbhs x) else globally [set x].

Variant nbhs_subspace_spec x : Prop -> Prop -> bool -> set_system T -> Type :=
  | WithinSubspace :
      A x -> nbhs_subspace_spec x True False true (within A (nbhs x))
  | WithoutSubspace :
    ~ A x -> nbhs_subspace_spec x False True false (globally [set x]).

Lemma nbhs_subspaceP_subproof x :
  nbhs_subspace_spec x (A x) (~ A x) (x \in A) (nbhs_subspace x).
Proof.
rewrite /nbhs_subspace; case:(boolP (x \in A)); rewrite ?(inE, notin_setE) => xA.
  by rewrite (@propext (A x) True)// not_True; constructor.
by rewrite (@propext (A x) False)// not_False; constructor.
Qed.

Lemma nbhs_subspace_in (x : T) : A x -> within A (nbhs x) = nbhs_subspace x.
Proof. by case: nbhs_subspaceP_subproof. Qed.

Lemma nbhs_subspace_out (x : T) : ~ A x -> globally [set x] = nbhs_subspace x.
Proof. by case: nbhs_subspaceP_subproof. Qed.

Lemma nbhs_subspace_filter (x : subspace A) : ProperFilter (nbhs_subspace x).
Proof.
case: nbhs_subspaceP_subproof => ?; last exact: globally_properfilter.
by apply: within_nbhs_proper; apply: subset_closure.
Qed.

HB.instance Definition _ := Choice.copy (subspace A) _.

HB.instance Definition _ := hasNbhs.Build (subspace A) nbhs_subspace.

Lemma nbhs_subspaceP (x : subspace A) :
  nbhs_subspace_spec x (A x) (~ A x) (x \in A) (nbhs x).
Proof. exact: nbhs_subspaceP_subproof. Qed.

Lemma nbhs_subspace_singleton (p : subspace A) B : nbhs p B -> B p.
Proof. by case: nbhs_subspaceP => ? => [/nbhs_singleton|]; apply. Qed.

Lemma nbhs_subspace_nbhs (p : subspace A) B : nbhs p B -> nbhs p (nbhs^~ B).
Proof.
case: nbhs_subspaceP => [|] Ap.
  by move=> /nbhs_interior; apply: filterS => y A0y Ay; case: nbhs_subspaceP.
by move=> E x ->; case: nbhs_subspaceP.
Qed.

HB.instance Definition _ := Nbhs_isNbhsTopological.Build (subspace A)
  nbhs_subspace_filter nbhs_subspace_singleton nbhs_subspace_nbhs.

Lemma subspace_cvgP (F : set_system T) (x : T) : Filter F -> A x ->
  (F --> (x : subspace A)) <-> (F --> within A (nbhs x)).
Proof. by case: _ / nbhs_subspaceP. Qed.

Lemma subspace_continuousP {S : topologicalType} (f : T -> S) :
  continuous (f : subspace A -> S) <->
  (forall x, A x -> f @ within A (nbhs x) --> f x) .
Proof.
split => [ctsf x Ax W /=|wA x].
  by rewrite nbhs_simpl //= nbhs_subspace_in //=; apply: ctsf.
rewrite /continuous_at; case: _ / (nbhs_subspaceP x) => Ax.
  exact: (cvg_trans _ (wA _ Ax)).
by move=> ? /nbhs_singleton //= ?; rewrite nbhs_simpl => ? ->.
Qed.

Lemma subspace_eq_continuous {S : topologicalType} (f g : subspace A -> S) :
  {in A, f =1 g} -> continuous f -> continuous g.
Proof.
rewrite ?subspace_continuousP => feq L x Ax; rewrite -(feq x) ?inE //.
by apply: cvg_trans _ (L x Ax); apply: fmap_within_eq=> ? ?; rewrite feq.
Qed.

Lemma continuous_subspace_in {U : topologicalType} (f : subspace A -> U) :
  continuous f = {in A, continuous f}.
Proof.
rewrite propeqE in_setP subspace_continuousP /continuous_at //=; split.
  by move=> Q x Ax; case: (nbhs_subspaceP x) => //=; exact: Q.
by move=> + x Ax => /(_ x Ax); case: (nbhs_subspaceP x) => //=; exact: Q.
Qed.

Lemma nbhs_subspace_interior (x : T) :
  A° x -> nbhs x = (nbhs (x : subspace A)).
Proof.
move=> /[dup] /[dup] /interior_subset ? /within_interior <- ?.
by case: RHS / nbhs_subspaceP.
Qed.

Lemma nbhs_subspace_ex (U : set T) (x : T) : A x ->
  nbhs (x : subspace A) U <->
  exists2 V, nbhs (x : T) V & U `&` A = V `&` A.
Proof. by case: (nbhs _) / nbhs_subspaceP; rewrite // ?withinE. Qed.

Lemma incl_subspace_continuous : continuous incl_subspace.
Proof. by apply/subspace_continuousP => x Ax; apply: cvg_within. Qed.

Section SubspaceOpen.

Lemma open_subspace1out (x : subspace A) : ~ A x -> open [set x].
Proof.
move=> /nbhs_subspace_out E; have : nbhs x [set x] by rewrite /nbhs //= -E.
rewrite nbhsE => [[U []]] oU Ux Usub; suff : U = [set x] by move=> <-.
by rewrite eqEsubset; split => // t ->.
Qed.

Lemma open_subspace_out (U : set (subspace A)) : U `<=` ~` A -> open U.
Proof.
move=> Usub; rewrite (_ : U = \bigcup_(i in U) [set i]).
  by apply: bigcup_open => ? ?; apply: open_subspace1out; exact: Usub.
by rewrite eqEsubset; split => x; [move=> ?; exists x|case=> i ? ->].
Qed.

Lemma open_subspaceT : open (A : set (subspace A)).
Proof. by move=> ?; case: nbhs_subspaceP => //= ? ?; apply: withinT. Qed.

Lemma open_subspaceIT (U : set (subspace A)) : open (U `&` A) = open U.
Proof.
apply/propext; split; last first.
  by move=> oU; apply: openI => //; apply: open_subspaceT.
move=> oUA; rewrite (_ : U = (U `&` A) `|` (U `&` ~`A)).
  by apply: openU => //; apply: open_subspace_out => ? [].
by rewrite -setIUr setUCr setIT.
Qed.

Lemma open_subspaceTI (U : set (subspace A)) :
  open (A `&` U : set (subspace A)) = open U.
Proof. by rewrite setIC open_subspaceIT. Qed.

Lemma closed_subspaceT : closed (A : set (subspace A)).
Proof.
rewrite -(setCK A);
by apply: open_closedC; rewrite -open_subspaceIT setICl; exact: open0.
Qed.

Lemma open_subspaceP (U : set T) :
  open (U : set (subspace A)) <->
  exists V, open (V : set T) /\ V `&` A = U `&` A.
Proof.
split; first last.
  case=> V [oV UV]; rewrite -open_subspaceIT -UV.
  move=> x //= []; case: nbhs_subspaceP; rewrite //= withinE.
  move=> ? ? _; exists V; last by rewrite -setIA setIid.
  by move: oV; rewrite openE /interior; apply.
rewrite -open_subspaceIT => oUA.
have oxF : forall x : T, (U `&` A) x ->
    exists V, (open_nbhs (x : T) V) /\ (V `&` A `<=` U `&` A).
  move=> x /[dup] UAx /= [??]; move: (oUA _ UAx);
    case: nbhs_subspaceP => // ?.
  rewrite withinE /= => [[V nbhsV UV]]; rewrite -setIA setIid in UV.
  exists V°; split; first rewrite open_nbhsE; first split => //.
  - exact: open_interior.
  - exact: nbhs_interior.
  - by rewrite UV=> t [/interior_subset] ??; split.
pose f (x : T) :=
  if pselect ((U `&` A) x) is left e then projT1 (cid (oxF x e)) else set0.
set V := \bigcup_(x in (U `&` A)) (f x); exists V; split.
  apply: bigcup_open => i UAi; rewrite /f; case: pselect => // ?; case: (cid _).
  by move=> //= W; rewrite open_nbhsE=> -[[]].
rewrite eqEsubset /V /f; split.
  move=> t [[u]] UAu /=; case: pselect => //= ?.
  by case: (cid _) => //= W [] _ + ? ?; apply; split.
move=> t UAt; split => //; last by case: UAt.
exists t => //; case: pselect => //= [[? ?]].
by case: (cid _) => //= W [] [] _.
Qed.

Lemma closed_subspaceP (U : set T) :
  closed (U : set (subspace A)) <->
  exists V, closed (V : set T) /\ V `&` A = U `&` A.
Proof.
rewrite -openC open_subspaceP.
under [X in _ <-> X] eq_exists => V do rewrite -openC.
by split => -[V [? VU]]; exists (~` V); split; rewrite ?setCK //;
  move/(congr1 setC): VU; rewrite ?eqEsubset ?setCI ?setCK; firstorder.
Qed.

Lemma open_subspaceW (U : set T) :
  open (U : set T) -> open (U : set (subspace A)).
Proof. by move=> oU; apply/open_subspaceP; exists U. Qed.

Lemma closed_subspaceW (U : set T) :
  closed (U : set T) -> closed (U : set (subspace A)).
Proof.  by move=> /closed_openC/open_subspaceW/open_closedC; rewrite setCK. Qed.

Lemma open_setIS (U : set (subspace A)) : open A ->
  open (U `&` A : set T) = open U.
Proof.
move=> oA; apply/propext; rewrite open_subspaceP.
split=> [|[V [oV <-]]]; last exact: openI.
by move=> oUA; exists (U `&` A); rewrite -setIA setIid.
Qed.

Lemma open_setSI (U : set (subspace A)) : open A -> open (A `&` U) = open U.
Proof. by move=> oA; rewrite -setIC open_setIS. Qed.

Lemma closed_setIS (U : set (subspace A)) : closed A ->
  closed (U `&` A : set T) = closed U.
Proof.
move=> oA; apply/propext; rewrite closed_subspaceP.
split=> [|[V [oV <-]]]; last exact: closedI.
by move=> oUA; exists (U `&` A); rewrite -setIA setIid.
Qed.

Lemma closed_setSI (U : set (subspace A)) :
  closed A -> closed (A `&` U) = closed U.
Proof. by move=> oA; rewrite -setIC closed_setIS. Qed.

Lemma closure_subspaceW (U : set T) :
  U `<=` A -> closure (U : set (subspace A)) = closure (U : set T) `&` A.
Proof.
have /closed_subspaceP := (@closed_closure _ (U : set (subspace A))).
move=> [V] [clV VAclUA] /[dup] /(@closure_subset (subspace _)).
have /closure_id <- := closed_subspaceT => /setIidr <-; rewrite setIC.
move=> UsubA; rewrite eqEsubset; split.
  apply: setSI; rewrite closureE; apply: smallest_sub (@subset_closure _ U).
  by apply: closed_subspaceW; exact: closed_closure.
rewrite -VAclUA; apply: setSI; rewrite closureE //=; apply: smallest_sub => //.
apply: subset_trans (@subIsetl _ V A); rewrite VAclUA subsetI; split => //.
exact: (@subset_closure _ (U : set (subspace A))).
Qed.

End SubspaceOpen.

Lemma compact_subspaceIP (U : set T) :
  compact (U `&` A : set (subspace A)) <-> compact (U `&` A : set T).
Proof.
rewrite ?compact_ultra /=.
split=> + F UF FUA => /(_ F UF FUA) [x] [[Ux Ax] Fp].
  exists x; split=> //; move/subspace_cvgP: Fp => /(_ Ax) Fx.
  by apply: cvg_trans; [exact: Fx | exact: cvg_within].
exists x; split=> //; apply/subspace_cvgP => //.
rewrite withinE => W/= -[V nbhsV WV]; apply: filterS (V `&` (U `&` A)) _ _ _.
  by rewrite setIC -setIA [A `&` _]setIC -WV=>?[]?[].
by apply: filterI; rewrite nbhs_simpl //; exact: Fp.
Qed.

Lemma clopen_connectedP : connected A <->
  (forall U, @clopen (subspace A) U ->
    U `<=` A  -> U !=set0 -> U = A).
Proof.
split.
  move=> + U [/open_subspaceP oU /closed_subspaceP cU] UA U0; apply => //.
  - case: oU => V [oV VAUA]; exists V; rewrite // setIC VAUA.
    exact/esym/setIidPl.
  - case: cU => V [cV VAUA]; exists V => //; rewrite setIC VAUA.
    exact/esym/setIidPl.
move=> clpnA U Un0 [V oV UVA] [W cW UWA]; apply: clpnA => //; first split.
- by apply/open_subspaceP; exists V; rewrite setIC UVA setIAC setIid.
- by apply/closed_subspaceP; exists W; rewrite setIC UWA setIAC setIid.
- by rewrite UWA; exact: subIsetl.
Qed.

End Subspace.

HB.instance Definition _ {T : ptopologicalType} (A : set T) :=
  isPointed.Build (subspace A) point.

Global Instance subspace_filter {T : topologicalType}
    (A : set T) (x : subspace A) :
  Filter (nbhs_subspace x) := nbhs_subspace_filter x.

Global Instance subspace_proper_filter {T : topologicalType}
    (A : set T) (x : subspace A) :
  ProperFilter (nbhs_subspace x) := nbhs_subspace_filter x.

Definition from_subspace {T U : Type} (A : set T) (f : T -> U) : subspace A -> U :=
  f.
Arguments from_subspace {T U} A f.

Notation "{ 'within' A , 'continuous' f }" :=
  (continuous (from_subspace A f)) : classical_set_scope.

Arguments nbhs_subspaceP {T} A x.

Section SubspaceRelative.
Context {T : topologicalType}.
Implicit Types (U : topologicalType) (A B : set T).

Lemma nbhs_subspace_subset A B (x : T) :
  A `<=` B -> nbhs (x : subspace B) `<=` nbhs (x : subspace A).
Proof.
rewrite /= => AB; case: (nbhs_subspaceP A); case: (nbhs_subspaceP B).
- by move=> ? ?; apply: within_subset => //=; exact: (nbhs_filter x).
- by move=> ? /AB.
- by move=> Bx ? W /nbhs_singleton /(_ Bx) ? ? ->.
- by move=> ? ?.
Qed.

Lemma continuous_subspaceW {U} A B (f : T -> U) :
  A `<=` B ->
  {within B, continuous f} -> {within A, continuous f}.
Proof.
by move=> ? ctsF ? ? ?; apply: (@nbhs_subspace_subset A B) => //; exact: ctsF.
Qed.

Lemma nbhs_subspaceT (x : T) : nbhs (x : subspace setT) = nbhs x.
Proof.
have [_|] := nbhs_subspaceP [set: T]; last by cbn.
rewrite eqEsubset withinE; split => [W [V nbhsV]|W ?]; last by exists W.
by rewrite 2!setIT => ->.
Qed.

Lemma continuous_subspaceT_for {U} A (f : T -> U) (x : T) :
  A x -> {for x, continuous f} -> {for x, continuous (f : subspace A -> U)}.
Proof.
rewrite /continuous_at /prop_for => inA ctsf.
have [_|//] := nbhs_subspaceP A x.
apply: (cvg_trans _ ctsf); apply: cvg_fmap2; apply: cvg_within.
Qed.

Lemma continuous_in_subspaceT {U} A (f : T -> U) :
  {in A, continuous f} -> {within A, continuous f}.
Proof.
rewrite continuous_subspace_in ?in_setP => ctsf t At.
by apply: continuous_subspaceT_for => //=; apply: ctsf.
Qed.

Lemma continuous_subspaceT {U} A (f : T -> U) :
  continuous f -> {within A, continuous f}.
Proof.
move=> ctsf; rewrite continuous_subspace_in => ? ?.
exact: continuous_in_subspaceT.
Qed.

Lemma continuous_open_subspace {U} A (f : T -> U) :
  open A -> {within A, continuous f} = {in A, continuous f}.
Proof.
rewrite openE continuous_subspace_in /= => oA; rewrite propeqE ?in_setP.
by split => + x /[dup] Ax /oA Aox => /(_ _ Ax);
  rewrite /continuous_at -(nbhs_subspace_interior Aox).
Qed.

Lemma continuous_inP {U} A (f : T -> U) : open A ->
  {in A, continuous f} <-> forall X, open X -> open (A `&` f @^-1` X).
Proof.
move=> oA; rewrite -continuous_open_subspace// continuousP.
by under eq_forall do rewrite -open_setSI//.
Qed.

(* pasting lemma *)
Lemma withinU_continuous {U} A B (f : T -> U) : closed A -> closed B ->
  {within A, continuous f} -> {within B, continuous f} ->
  {within A `|` B, continuous f}.
Proof.
move=> ? ? ctsA ctsB; apply/continuous_closedP => W oW.
case/continuous_closedP/(_ _ oW)/closed_subspaceP: ctsA => V1 [? V1W].
case/continuous_closedP/(_ _ oW)/closed_subspaceP: ctsB => V2 [? V2W].
apply/closed_subspaceP; exists ((V1 `&` A) `|` (V2 `&` B)); split.
  by apply: closedU; exact: closedI.
rewrite [RHS]setIUr -V2W -V1W eqEsubset; split=> ?.
  by case=> [[][]] ? ? [] ?; [left | left | right | right]; split.
by case=> [][] ? ?; split=> []; [left; split | left | right; split | right].
Qed.

Lemma subspaceT_continuous {U} A (B : set U) (f : {fun A >-> B}) :
  {within A, continuous f} -> continuous (f : subspace A -> subspace B).
Proof.
move=> /continuousP ctsf; apply/continuousP => O /open_subspaceP [V [oV VBOB]].
rewrite -open_subspaceIT; apply/open_subspaceP.
case/open_subspaceP: (ctsf _ oV) => W [oW fVA]; exists W; split => //.
rewrite fVA -setIA setIid eqEsubset; split => x [fVx Ax]; split => //.
- by have /[!VBOB]-[] : (V `&` B) (f x) by split => //; exact: funS.
- by have /[!esym VBOB]-[] : (O `&` B) (f x) by split => //; exact: funS.
Qed.

Lemma continuous_subspace0 {U} (f : T -> U) : {within set0, continuous f}.
Proof.
move=> x Q /=.
by case: (nbhs_subspaceP (@set0 T) x) => // _ /nbhs_singleton /= ? ? ->.
Qed.

Lemma continuous_subspace1 {U} (a : T) (f : T -> U) :
  {within [set a], continuous f}.
Proof.
move=> x Q /=.
case: (nbhs_subspaceP [set a] x); last by move=> _ /nbhs_singleton /= ? ? ->.
by move=> -> /nbhs_singleton ?; apply: nearW => ? ->.
Qed.

End SubspaceRelative.

Section SubspaceUniform.
Local Open Scope relation_scope.
Context {X : uniformType} (A : set X).

Definition subspace_ent :=
  filter_from (@entourage X)
  (fun E => [set xy | (xy.1 = xy.2) \/ (A xy.1 /\ A xy.2 /\ E xy)]).

Let Filter_subspace_ent : Filter subspace_ent.
Proof.
apply: filter_from_filter; first by (exists setT; exact: filterT).
move=> P Q entP entQ; exists (P `&` Q); first exact: filterI.
move=> [x y] /=; case; first (by move=> ->; split=> /=; left).
by move=> [Ax [Ay [Pxy Qxy]]]; split=> /=; right.
Qed.

Let subspace_uniform_entourage_diagonal :
  forall X : set (subspace A * subspace A),
    subspace_ent X -> diagonal `<=` X.
Proof. by move=> ? + [x y]/diagonalP ->; case=> V entV; apply; left. Qed.

Let subspace_uniform_entourage_inv : forall A : set (subspace A * subspace A),
  subspace_ent A -> subspace_ent A^-1.
Proof.
move=> ?; case=> V ? Vsub; exists V^-1; first exact: entourage_inv.
move=> [x y] /= G; apply: Vsub; case: G; first by (move=> <-; left).
by move=> [? [? Vxy]]; right; repeat split.
Qed.

Let subspace_uniform_entourage_split_ex :
  forall A : set (subspace A * subspace A),
    subspace_ent A -> exists2 B, subspace_ent B & B \; B `<=` A.
Proof.
move=> ?; case=> E entE Esub.
exists  [set xy | xy.1 = xy.2 \/ A xy.1 /\ A xy.2 /\ split_ent E xy].
  by exists (split_ent E).
move=> [x y] [z /= Ez zE] /=; case: Ez; case: zE.
  - by move=> -> ->; apply: Esub; left.
  - move=> [ ? []] ? G xy; subst; apply: Esub; right; repeat split => //=.
    by apply: entourage_split => //=; first exact: G; exact: entourage_refl.
  - move=> -> [ ? []] ? G; apply: Esub; right; repeat split => //=.
    by apply: entourage_split => //=; first exact: G; exact: entourage_refl.
  - move=> []? []? ?[]?[]??; apply: Esub; right; repeat split => //=.
    by apply: subset_split_ent => //; exists z.
Qed.

Let subspace_uniform_nbhsE : @nbhs _ (subspace A) = nbhs_ subspace_ent.
Proof.
pose EA := [set xy | xy.1 = xy.2 \/ A xy.1 /\ A xy.2].
have entEA : subspace_ent EA.
  exists setT; first exact: filterT.
  by move=> [??] /= [ ->|[?] [?]];[left|right].
rewrite funeq2E=> x U.
case: (@nbhs_subspaceP X A x); rewrite propeqE; split => //=.
- rewrite withinE; case=> V /[dup] nbhsV => [/nbhsP [E entE Esub] UV].
  exists [set xy | xy.1 = xy.2 \/ A xy.1 /\ A xy.2 /\ E xy].
    by exists E => //= [[? ?]] /= [->| [? []]//]; exact: entourage_refl.
  move=> y /= /xsectionP/= -[<-{y}|].
    suff : (U `&` A) x by case.
    by rewrite UV; split => //; exact: (@nbhs_singleton X).
  case=> _ [Ay Ey]; suff : (U `&` A) y by case.
  by rewrite UV; split => //; exact/Esub/xsectionP.
- move=> [] W [E eentE subW] subU //=.
  near=> w; apply/subU/xsectionP/subW; right; repeat split => //=.
    exact: (near (withinT _ (@nbhs_filter X _))).
  by near: w; apply/nbhsP; exists E => // y /xsectionP.
- move=> //= Ux; exists EA => //.
  by move=> y /xsectionP => -[|[]] //= <-; exact: Ux.
- rewrite //= => [[W [W' entW' subW] subU]] ? ->.
  by apply/subU/xsectionP/subW; left.
Unshelve. all: by end_near. Qed.

HB.instance Definition _ := Nbhs_isUniform_mixin.Build (subspace A)
  Filter_subspace_ent subspace_uniform_entourage_diagonal
  subspace_uniform_entourage_inv subspace_uniform_entourage_split_ex
  subspace_uniform_nbhsE.

End SubspaceUniform.

Section SubspacePseudoMetric.
Context {R : numDomainType} {X : pseudoMetricType R} (A : set X).
Implicit Type e : R.

Definition subspace_ball (x : subspace A) (r : R) :=
  if x \in A then A `&` ball (x : X) r else [set x].

Let subspace_pm_ball_center x e : 0 < e -> subspace_ball x e x.
Proof.
rewrite /subspace_ball; case: ifP => //= /asboolP ? ?.
by split=> //; exact: ballxx.
Qed.

Let subspace_pm_ball_sym x y e :
  subspace_ball x e y -> subspace_ball y e x.
Proof.
rewrite /subspace_ball; case: ifP => //= /asboolP ?.
  by move=> [] Ay /ball_sym yBx; case: ifP => /asboolP.
by move=> ->; case: ifP => /asboolP.
Qed.

Let subspace_pm_ball_triangle x y z e1 e2 :
  subspace_ball x e1 y -> subspace_ball y e2 z -> subspace_ball x (e1 + e2) z.
Proof.
rewrite /subspace_ball; (repeat case: ifP => /asboolP).
- by move=>?? [??] [??]; split => //=; apply: ball_triangle; eauto.
- by move=> ?? [??] ->.
- by move=> + /[swap] => /[swap] => ->.
- by move=> _ _ -> ->.
Qed.

Let subspace_pm_entourageE :
  @entourage (subspace A) = entourage_ subspace_ball.
Proof.
rewrite eqEsubset; split; rewrite /subspace_ball.
  move=> U [W + subU]; rewrite -entourage_ballE => [[eps] nneg subW].
  exists eps => //; apply: (subset_trans _ subU).
  move=> [x y] /=; case: ifP => /asboolP ?.
    by move=> [Ay xBy]; right; repeat split => //; exact: subW.
  by move=> ->; left.
move=> E [eps nneg subE]; exists [set xy | ball (xy.1 : X) eps xy.2].
  by rewrite -entourage_ballE; exists eps.
move=> [x y] /= [->|[]Ax []Ay xBy]; apply: subE => //=.
  by case: ifP => /asboolP; split => //; exact: ballxx.
by case: ifP => /asboolP.
Qed.

HB.instance Definition _ :=
  @Uniform_isPseudoMetric.Build R (subspace A) subspace_ball
    subspace_pm_ball_center subspace_pm_ball_sym subspace_pm_ball_triangle
    subspace_pm_entourageE.

Lemma ball_subspace_ball (x : subspace A) r (y : subspace A) :
  ball x r y = subspace_ball x r y.
Proof. by []. Qed.

End SubspacePseudoMetric.

Section SubspaceWeak.
Context {T : topologicalType} {U : choiceType}.
Variables (f : U -> T).

Lemma weak_subspace_open (A : set (weak_topology f)) :
  open A -> open (f @` A : set (subspace (range f))).
Proof.
case=> B oB <-; apply/open_subspaceP; exists B; split => //; rewrite eqEsubset.
split => z [] /[swap]; first by case=> w _ <- ?; split; exists w.
by case=> w _ <- [v] ? <-.
Qed.

End SubspaceWeak.

Lemma continuous_compact {T U : topologicalType} (f : T -> U) A :
  {within A, continuous f} -> compact A -> compact (f @` A).
Proof.
move=> fcont Aco F FF FfA; set G := filter_from F (fun C => A `&` f @^-1` C).
have GF : ProperFilter G.
  apply: (filter_from_proper (filter_from_filter _ _)).
  - by exists (f @` A).
  - by move=> C1 C2 F1 F2; exists (C1 `&` C2); [exact: filterI|move=> ? [? []]].
  - by move=> C /(filterI FfA) /filter_ex [_ [[p ? <-]]]; exists p.
move: Aco; rewrite -[A]setIid => /compact_subspaceIP; rewrite setIid.
case /(_ G); first by exists (f @` A) => // ? [].
move=> p [Ap clsGp]; exists (f p); split; first exact/imageP.
move=> B C FB /fcont p_Cf.
have : G (A `&` f @^-1` B) by exists B.
by move=> /clsGp /(_ p_Cf) [q [[]]]; exists (f q).
Qed.

Lemma connected_continuous_connected (T U : topologicalType)
    (A : set T) (f : T -> U) :
  connected A -> {within A, continuous f} -> connected (f @` A).
Proof.
move=> cA cf; apply: contrapT => /connectedPn[E [E0 fAE sE]].
set AfE := fun b =>(A `&` f @^-1` E b) : set (subspace A).
suff sAfE : separated (AfE false) (AfE true).
  move: cA; apply/connectedPn; exists AfE; split; last (rewrite /AfE; split).
  - move=> b; case: (E0 b) => /= u Ebu.
    have [t Et ftu] : (f @` A) u by rewrite fAE; case: b Ebu; [right|left].
    by exists t; split => //=; rewrite /preimage ftu.
  - by rewrite -setIUr -preimage_setU -fAE; exact/esym/setIidPl/preimage_image.
  + rewrite -{2}(setIid A) ?setIA -(@closure_subspaceW _ A); last by move=> ?[].
    by rewrite -/(AfE false) -setIA -/(AfE true); case: sAfE.
  + rewrite -{1}(setIid A) setIC ?setIA -(@closure_subspaceW _ A).
      by rewrite -/(AfE true) -setIA -/(AfE false) setIC; case: sAfE.
    by move=> ?[].
suff cI0 b : closure (AfE b) `&` AfE (~~ b) = set0.
  by rewrite /separated cI0 setIC cI0.
have [fAfE cEIE] :
    f @` AfE (~~ b) = E (~~ b) /\ closure (E b) `&` E (~~ b) = set0.
  split; last by case: sE => ? ?; case: b => //; rewrite setIC.
  rewrite eqEsubset; split => [|u Ebu].
    apply: (subset_trans sub_image_setI).
    by apply: subIset; right; exact: image_preimage_subset.
  have [t [At ftu]] : exists t, A t /\ f t = u.
    suff [t At ftu] : (f @` A) u by exists t.
    by rewrite fAE; case: b Ebu; [left|right].
  by exists t => //; split => //=; rewrite /preimage ftu.
have ? : f @` closure (AfE b) `<=` closure (E b).
  have /(@image_subset _ _ f) : closure (AfE b) `<=` f @^-1` closure (E b).
    have /closure_id -> : closed (f @^-1` closure (E b) : set (subspace A)).
      by apply: closed_comp => //; exact: closed_closure.
    apply: closure_subset.
    have /(@preimage_subset _ _ f) A0cA0 := @subset_closure _ (E b).
    by apply: subset_trans A0cA0; apply: subIset; right.
  by move/subset_trans; apply; exact: image_preimage_subset.
apply/nonemptyPn => -[t [AfEb AfENb]].
have : f @` closure (AfE b) `&` f @` AfE (~~ b) = set0.
  by rewrite fAfE; exact: subsetI_eq0 cEIE.
by rewrite predeqE => /(_ (f t)) [fcAfEb] _; apply: fcAfEb; split; exists t.
Qed.

Lemma continuous_localP {X Y : topologicalType} (f : X -> Y) :
  continuous f <->
  forall (x : X), \forall U \near powerset_filter_from (nbhs x),
    {within U, continuous f}.
Proof.
split; first by move=> ? ?; near=> U; apply: continuous_subspaceT=> ?; exact.
move=> + x => /(_ x)/near_powerset_filter_fromP.
case; first by move=> ? ?; exact: continuous_subspaceW.
move=> U nbhsU wctsf; wlog oU : U wctsf nbhsU / open U.
  move: nbhsU; rewrite nbhsE => -[] W [oW Wx WU] /(_ W).
  by move/(_ (continuous_subspaceW WU wctsf)); apply => //; exists W.
move/nbhs_singleton: nbhsU; move: x; apply/in_setP.
by rewrite -continuous_open_subspace.
Unshelve. end_near. Qed.

Lemma continuous_subspace_setT {T U : topologicalType} (f : T -> U) :
  continuous f <-> {within setT, continuous f}.
Proof. by split => + x K nfK=> /(_ x K nfK); rewrite nbhs_subspaceT. Qed.

Section subspace_product.
Context {X Y Z : topologicalType} (A : set X) (B : set Y) .

Lemma nbhs_prodX_subspace_inE x : (A `*` B) x ->
  nbhs  (x : subspace (A `*` B)) = @nbhs _ (subspace A * subspace B)%type x.
Proof.
case: x => a b [/= Aa Bb]; rewrite /nbhs/= -nbhs_subspace_in//.
rewrite funeqE => U /=; rewrite propeqE; split; rewrite /nbhs /=.
  move=> [[P Q]] /= [nxP nyQ] PQABU; exists (P `&` A, Q `&` B).
    by split; apply/nbhs_subspace_ex => //=; [exists P | exists Q];
      rewrite // -setIA setIid.
  by case=> p q [[/= Pp Ap [Qq Bq]]]; exact: PQABU.
move=> [[P Q]] /= [/(nbhs_subspace_ex _ Aa) [P' P'a PPA]].
move/(nbhs_subspace_ex _ Bb) => [Q' Q'a QQB PQU].
exists (P', Q') => //= -[p q] [P'p Q'q] [Ap Bq]; apply: PQU; split => /=.
  by have [] : (P `&` A) p by rewrite PPA.
by have [] : (Q `&` B) q by rewrite QQB.
Qed.

Lemma continuous_subspace_prodP (f : X * Y -> Z) :
  {in A `*` B, continuous (f : subspace A * subspace B -> Z)} <->
  {within A `*` B, continuous f}.
Proof.
by split; rewrite continuous_subspace_in => + x ABx U nfxU => /(_ x ABx U nfxU);
  rewrite nbhs_prodX_subspace_inE//; move/set_mem: ABx.
Qed.
End subspace_product.

#[short(type = "continuousFunType")]
HB.structure Definition ContinuousFun {X Y : topologicalType}
    (A : set X) (B : set Y) :=
  {f of @isFun (subspace A) Y A B f & @Continuous (subspace A) Y f }.

Section continuous_fun_comp.
Context {X Y Z : topologicalType} (A : set X) (B : set Y) (C : set Z).
Context {f : continuousFunType A B} {g : continuousFunType B C}.

Local Lemma continuous_comp_subproof : continuous (g \o f : subspace A -> Z).
Proof.
move=> x; apply: continuous_comp; last exact: cts_fun.
exact/subspaceT_continuous/cts_fun.
Qed.

HB.instance Definition _ :=
  @isContinuous.Build (subspace A) Z (g \o f) continuous_comp_subproof.

End continuous_fun_comp.
