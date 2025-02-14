(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum finmap matrix.
From mathcomp Require Import rat interval zmodp vector fieldext falgebra.
From mathcomp Require Import archimedean.
From mathcomp Require Import boolp classical_sets functions cardinality.
From mathcomp Require Import set_interval ereal reals itv topology.
From mathcomp Require Import prodnormedzmodule function_spaces.
From mathcomp Require Import separation_axioms.

(**md**************************************************************************)
(* # Topological vector spaces                                                *)
(*                                                                            *)
(* This file introduces locally convex topological vector spaces.             *)
(* ```                                                                        *)
(*            NbhsNmodule == HB class, join of Nbhs and Nmodule               *)
(*            NbhsZmodule == HB class, join of Nbhs and Zmodule               *)
(*          NbhsLmodule K == HB class, join of Nbhs and Lmodule over K        *)
(*                           K is a numDomainType.                            *)
(*     TopologicalNmodule == HB class, joint of Topological and Nmodule       *)
(*     TopologicalZmodule == HB class, joint of Topological and Zmodule       *)
(*  topologicalLmodType K == topological space and Lmodule over K             *)
(*                           K is a numDomainType.                            *)
(*                           The HB class is TopologicalLmodule.              *)
(*         UniformZmodule == HB class, joint of Uniform and Zmodule           *)
(*       UniformLmodule K == HB class, joint of Uniform and Lmodule over K    *)
(*                           K is a numDomainType.                            *)
(*               convex A == A : set M is a convex set of elements of M       *)
(*                           M is an Lmodule over R : numDomainType.          *)
(*             tvsType R  == interface type for a locally convex topological  *)
(*                           vector space on a numDomain R                    *)
(*                           A tvs is constructed over a uniform space.       *)
(*                           The HB class is Tvs.                             *)
(*  TopologicalLmod_isTvs == factory allowing the construction of a tvs from  *)
(*                           an Lmodule which is also a topological space.    *)
(*  ```                                                                       *)
(* HB instances:                                                              *)
(* - The type R^o (R : numFieldType) is endowed with the structure of Tvs.    *)
(* - The product of two Tvs is endowed with the structure of Tvs.             *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* HB.structure Definition PointedNmodule := {M of Pointed M & GRing.Nmodule M}. *)
(* HB.structure Definition PointedZmodule := {M of Pointed M & GRing.Zmodule M}. *)
(* HB.structure Definition PointedLmodule (K : numDomainType) := *)
(*   {M of Pointed M & GRing.Lmodule K M}. *)

(* HB.structure Definition FilteredNmodule := {M of Filtered M M & GRing.Nmodule M}. *)
(* HB.structure Definition FilteredZmodule := {M of Filtered M M & GRing.Zmodule M}. *)
(* HB.structure Definition FilteredLmodule (K : numDomainType) := *)
(*   {M of Filtered M M & GRing.Lmodule K M}. *)
HB.structure Definition NbhsNmodule := {M of Nbhs M & GRing.Nmodule M}.
HB.structure Definition NbhsZmodule := {M of Nbhs M & GRing.Zmodule M}.
HB.structure Definition NbhsLmodule (K : numDomainType) :=
  {M of Nbhs M & GRing.Lmodule K M}.

HB.structure Definition TopologicalNmodule :=
  {M of Topological M & GRing.Nmodule M}.
HB.structure Definition TopologicalZmodule :=
  {M of Topological M & GRing.Zmodule M}.

#[short(type="topologicalLmodType")]
HB.structure Definition TopologicalLmodule (K : numDomainType) :=
  {M of Topological M & GRing.Lmodule K M}.

HB.structure Definition UniformZmodule := {M of Uniform M & GRing.Zmodule M}.
HB.structure Definition UniformLmodule (K : numDomainType) :=
  {M of Uniform M & GRing.Lmodule K M}.

Definition convex (R : numDomainType) (M : lmodType R) (A : set M) :=
  forall x y (lambda : R), x \in A -> y \in A ->
  0 < lambda -> lambda < 1 -> lambda *: x + (1 - lambda) *: y \in A.

HB.mixin Record Uniform_isTvs (R : numDomainType) E
    of Uniform E & GRing.Lmodule R E := {
  add_continuous : continuous (fun x : E * E => x.1 + x.2) ;
  scale_continuous : continuous (fun z : R^o * E => z.1 *: z.2) ;
  locally_convex : exists2 B : set (set E),
    (forall b, b \in B -> convex b) & basis B
}.

#[short(type="tvsType")]
HB.structure Definition Tvs (R : numDomainType) :=
  {E of Uniform_isTvs R E & Uniform E & GRing.Lmodule R E}.

Section properties_of_topologicalLmodule.
Context (R : numDomainType) (E : topologicalLmodType R) (U : set E).

Lemma nbhsN_subproof (f : continuous (fun z : R^o * E => z.1 *: z.2)) (x : E) :
  nbhs x U -> nbhs (-x) (-%R @` U).
Proof.
move=> Ux; move: (f (-1, -x) U); rewrite /= scaleN1r opprK => /(_ Ux) [] /=.
move=> [B] B12 [B1 B2] BU; near=> y; exists (- y); rewrite ?opprK// -scaleN1r//.
apply: (BU (-1, y)); split => /=; last by near: y.
by move: B1 => [] ? ?; apply => /=; rewrite subrr normr0.
Unshelve. all: by end_near. Qed.

Lemma nbhs0N_subproof (f : continuous (fun z : R^o * E => z.1 *: z.2)) :
  nbhs 0 U -> nbhs 0 (-%R @` U).
Proof. by move => Ux; rewrite -oppr0; exact: nbhsN_subproof. Qed.

Lemma nbhsT_subproof (f : continuous (fun x : E * E => x.1 + x.2)) (x : E) :
  nbhs 0 U -> nbhs x (+%R x @` U).
Proof.
move => U0; have /= := f (x, -x) U; rewrite subrr => /(_ U0).
move=> [B] [B1 B2] BU; near=> x0.
exists (x0 - x); last by rewrite addrC subrK.
by apply: (BU (x0, -x)); split; [near: x0; rewrite nearE|exact: nbhs_singleton].
Unshelve. all: by end_near. Qed.

Lemma nbhsB_subproof (f : continuous (fun x : E * E => x.1 + x.2)) (z x : E) :
  nbhs z U -> nbhs (x + z) (+%R x @` U).
Proof.
move=> U0; have /= := f (x + z, -x) U; rewrite [x + z]addrC addrK.
move=> /(_ U0)[B] [B1 B2] BU; near=> x0.
exists (x0 - x); last by rewrite addrC subrK.
by apply: (BU (x0, -x)); split; [near: x0; rewrite nearE|exact: nbhs_singleton].
Unshelve. all: by end_near. Qed.

End properties_of_topologicalLmodule.

HB.factory Record TopologicalLmod_isTvs (R : numDomainType) E
    of Topological E & GRing.Lmodule R E := {
  add_continuous : continuous (fun x : E * E => x.1 + x.2) ;
  scale_continuous : continuous (fun z : R^o * E => z.1 *: z.2) ;
  locally_convex : exists2 B : set (set E),
    (forall b, b \in B -> convex b) & basis B
  }.

HB.builders Context R E of TopologicalLmod_isTvs R E.

Definition entourage : set_system (E * E) :=
  fun P => exists (U : set E), nbhs (0 : E) U  /\
                     (forall xy : E * E,  (xy.1 - xy.2) \in U -> xy \in P).

Let nbhs0N (U : set E) : nbhs (0 : E) U -> nbhs (0 : E) (-%R @` U).
Proof. exact/nbhs0N_subproof/scale_continuous. Qed.

Lemma nbhsN (U : set E) (x : E) : nbhs x U -> nbhs (-x) (-%R @` U).
Proof. exact/nbhsN_subproof/scale_continuous. Qed.

Let nbhsT (U : set E) (x : E) : nbhs (0 : E) U -> nbhs x (+%R x @`U).
Proof. exact/nbhsT_subproof/add_continuous. Qed.

Let nbhsB (U : set E) (z x : E) : nbhs z U -> nbhs (x + z) (+%R x @`U).
Proof. exact/nbhsB_subproof/add_continuous. Qed.

Lemma entourage_filter : Filter entourage.
Proof.
split; first by exists [set: E]; split; first exact: filter_nbhsT.
  move=> P Q; rewrite /entourage nbhsE /=.
  move=> [U [[B B0] BU Bxy]] [V [[C C0] CV Cxy]].
  exists (U `&` V); split => [|xy].
    by exists (B `&` C); [exact: open_nbhsI|exact: setISS].
  by rewrite !in_setI => /andP[/Bxy-> /Cxy->].
by move=> P Q PQ [U [HU Hxy]]; exists U; split=> [|xy /Hxy /[!inE] /PQ].
Qed.

Local Lemma entourage_refl (A : set (E * E)) :
  entourage A -> [set xy | xy.1 = xy.2] `<=` A.
Proof.
move=> [U [U0 Uxy]] xy eq_xy; apply/set_mem/Uxy; rewrite eq_xy subrr.
apply/mem_set; exact: nbhs_singleton.
Qed.

Local Lemma entourage_inv (A : set (E * E)) :
  entourage A -> entourage A^-1%relation.
Proof.
move=> [/= U [U0 Uxy]]; exists (-%R @` U); split; first exact: nbhs0N.
move=> xy /set_mem /=; rewrite -opprB => [[yx] Uyx] /oppr_inj yxE.
by apply/Uxy/mem_set; rewrite /= -yxE.
Qed.

Local Lemma entourage_split_ex (A : set (E * E)) : entourage A ->
  exists2 B : set (E * E), entourage B & (B \; B)%relation `<=` A.
Proof.
move=> [/= U] [U0 Uxy]; rewrite /entourage /=.
have := @add_continuous (0, 0); rewrite /continuous_at/= addr0 => /(_ U U0)[]/=.
move=> [W1 W2] []; rewrite nbhsE/= => [[U1 nU1 UW1] [U2 nU2 UW2]] Wadd.
exists [set w | (W1 `&` W2) (w.1 - w.2)].
  exists (W1 `&` W2); split; last by [].
  exists (U1 `&` U2); first exact: open_nbhsI.
  by move=> t [U1t U2t]; split; [exact: UW1|exact: UW2].
move => xy /= [z [H1 _] [_ H2]]; apply/set_mem/(Uxy xy)/mem_set.
rewrite [_ - _](_ : _ = (xy.1 - z) + (z - xy.2)); last by rewrite addrA subrK.
exact: (Wadd (xy.1 - z,z - xy.2)).
Qed.

Local Lemma nbhsE : nbhs = nbhs_ entourage.
Proof.
have lem : -1 != 0 :> R by rewrite oppr_eq0 oner_eq0.
rewrite /nbhs_ /=; apply/funext => x; rewrite /filter_from/=.
apply/funext => U; apply/propext => /=; rewrite /entourage /=; split.
- pose V : set E := [set v | x - v \in U].
  move=> nU; exists [set xy | xy.1 - xy.2 \in V]; last first.
    by move=> y /xsectionP; rewrite /V /= !inE /= opprB addrC subrK inE.
  exists V; split; last by move=> xy; rewrite !inE /= inE.
  have /= := nbhsB x (nbhsN nU); rewrite subrr /= /V.
  rewrite [X in nbhs _ X -> _](_ : _ = [set v | x - v \in U])//.
  apply/funext => /= v /=; rewrite inE; apply/propext; split.
    by move=> [x0 [x1]] Ux1 <- <-; rewrite opprB addrC subrK.
  move=> Uxy; exists (v - x); last by rewrite addrC subrK.
  by exists (x - v); rewrite ?opprB.
- move=> [A [U0 [nU UA]] H]; near=> z; apply: H; apply/xsectionP/set_mem/UA.
  near: z; rewrite nearE; have := nbhsT x (nbhs0N nU).
  rewrite [X in nbhs _ X -> _](_ : _ = [set v | x - v \in U0])//.
  apply/funext => /= z /=; apply/propext; split.
    by move=> [x0] [x1 Ux1 <-] <-; rewrite opprB addrC subrK inE.
  rewrite inE => Uxz; exists (z - x); last by rewrite addrC subrK.
  by exists (x - z); rewrite ?opprB.
Unshelve. all: by end_near. Qed.

HB.instance Definition _ := Nbhs_isUniform_mixin.Build E
    entourage_filter entourage_refl
    entourage_inv entourage_split_ex
    nbhsE.
HB.end.

Section Tvs_numDomain.
Context (R : numDomainType) (E : tvsType R) (U : set E).

Lemma nbhs0N : nbhs 0 U -> nbhs 0 (-%R @` U).
Proof. exact/nbhs0N_subproof/scale_continuous. Qed.

Lemma nbhsT (x :E) : nbhs 0 U -> nbhs x (+%R x @` U).
Proof. exact/nbhsT_subproof/add_continuous. Qed.

Lemma nbhsB (z x : E) : nbhs z U -> nbhs (x + z) (+%R x @` U).
Proof. exact/nbhsB_subproof/add_continuous. Qed.

End Tvs_numDomain.

Section Tvs_numField.

Lemma nbhs0Z (R : numFieldType) (E : tvsType R) (U : set E) (r : R) :
  r != 0 -> nbhs 0 U -> nbhs 0 ( *:%R r @` U ).
Proof.
move=> r0 U0; have /= := scale_continuous (r^-1, 0) U.
rewrite scaler0 => /(_ U0)[]/= B [B1 B2] BU.
near=> x => //=; exists (r^-1 *: x); last by rewrite scalerA divff// scale1r.
by apply: (BU (r^-1, x)); split => //=;[exact: nbhs_singleton|near: x].
Unshelve. all: by end_near. Qed.

Lemma nbhsZ  (R : numFieldType) (E : tvsType R) (U : set E) (r : R) (x :E) :
  r != 0 -> nbhs x U -> nbhs (r *:x) ( *:%R r @` U ).
Proof.
move=> r0 U0; have /= := scale_continuous ((r^-1, r *: x)) U.
rewrite scalerA mulVf// scale1r =>/(_ U0)[] /= B [B1 B2] BU.
near=> z; exists (r^-1 *: z); last by rewrite scalerA divff// scale1r.
by apply: (BU (r^-1,z)); split; [exact: nbhs_singleton|near: z].
Unshelve. all: by end_near. Qed.

End Tvs_numField.

Section standard_topology.
Variable R : numFieldType.

Local Lemma standard_add_continuous : continuous (fun x : R^o * R^o => x.1 + x.2).
Proof.
(* NB(rei): almost the same code as in normedtype.v *)
move=> [/= x y]; apply/cvg_ballP => e e0 /=.
exists (ball x (e / 2), ball y (e / 2)) => /=.
  by split; apply: nbhsx_ballx; rewrite divr_gt0.
rewrite /ball /ball_/= => xy /= [nx ny].
by rewrite opprD addrACA (le_lt_trans (ler_normD _ _)) // (splitr e) ltrD.
Qed.

Local Lemma standard_scale_continuous : continuous (fun z : R^o * R^o => z.1 *: z.2).
Proof.
(* NB: This lemma is proved once again in normedtype, in a shorter way with much more machinery *)
(*     To be rewritten once normedtype is split and tvs can depend on these lemmas *)
move=> [k x]; apply/cvg_ballP => e le0 /=.
pose M : R := maxr (`|e| + 1) (maxr `|k| (`|x| + `|x| + 2^-1 + 1)).
have M0l : 0 < `|e| + 1 by rewrite ltr_wpDl.
have M0r : 0 < maxr `|k| (`|x| + `|x| + 2^-1 + 1).
  rewrite comparable_lt_max; last exact/real_comparable.
  by rewrite normr_gt0; case: eqP => /=.
have Me : `|e| < M.
  rewrite (@lt_le_trans _ _ (`|e| + 1)) ?ltrDl//.
  have /= -> := num_le_max (`|e| + 1) (PosNum M0l) (PosNum M0r).
  by rewrite lexx.
have M0 : 0 < M by apply: le_lt_trans Me.
pose r := `|e| / 2 / M.
exists (ball k r, ball x r) => [|[z1 z2] [k1r k2r]].
  by split; exists r; rewrite //= ?divr_gt0 //= normr_gt0 gt_eqF.
have := @ball_split _ _ (k * z2)  (k * x)  (z1 * z2) `|e|.
rewrite /ball/= real_lter_normr ?gtr0_real//.
rewrite (_ : _ < - e = false) ?orbF; last by rewrite ltr_nnorml// oppr_le0 ltW.
apply.
  rewrite -mulrBr normrM (@le_lt_trans _ _ (M * `|x - z2|)) ?ler_wpM2r//.
    have /= -> := num_le_max `|k| (PosNum M0l) (PosNum M0r).
    by apply/orP; right; rewrite /maxr; case: ifPn => // /ltW.
  by rewrite -ltr_pdivlMl ?(lt_le_trans k2r)// mulrC.
rewrite -mulrBl normrM (@le_lt_trans _ _ (`|k - z1| * M)) ?ler_wpM2l//.
  rewrite (@le_trans _ _ (`|z2| + `|x|))// ?lerDl ?normr_ge0//.
  have z2xe : `|z2| <= `|x| + r.
    by rewrite -lerBlDl -(normrN x) (le_trans (lerB_normD _ _))// distrC ltW.
  rewrite (@le_trans _ _ (`|x| + r + `|x|)) ?lerD// addrC.
  rewrite [leRHS](_ : _ = M^-1 * (M *  M)); last first.
    by rewrite mulrA mulVf ?mul1r// gt_eqF.
  rewrite [leLHS](_ : _ = M^-1 * (M * (`|x| + `|x|) + `|e| / 2)); last first.
    by rewrite mulrDr mulrA mulVf ?mul1r ?gt_eqF// mulrC addrA.
  rewrite ler_wpM2l// ?invr_ge0// ?ltW// -ltrBrDl -mulrBr ltr_pM// ltrBrDl//.
  rewrite (@lt_le_trans _ _ (`|x| + `|x| + 2^-1 + 1)) //.
    by rewrite ltrDl ltr01.
  rewrite (num_le_max _ (PosNum M0l) (PosNum M0r))//=.
  apply/orP; right; have [->|k0] := eqVneq k 0.
    by rewrite normr0 comparable_le_max ?real_comparable// lexx orbT.
  have nk0 : 0 < `|k| by rewrite normr_gt0.
  have xx21 : 0 < `|x| + `|x| + 2^-1 + 1%R by rewrite addr_gt0.
  by rewrite (num_le_max _ (PosNum nk0) (PosNum xx21))// lexx orbT.
by rewrite -ltr_pdivlMr ?(lt_le_trans k1r) ?normr_gt0.
Qed.

Local Lemma standard_locally_convex :
  exists2 B : set (set R^o), (forall b, b \in B -> convex b) & basis B.
Proof.
(* NB(rei): almost the same code as in normedtype.v *)
exists [set B | exists x r, B = ball x r].
  move=> b; rewrite inE /= => [[x]] [r] -> z y l.
  rewrite !inE /ball /= => zx yx l0; rewrite -subr_gt0 => l1.
  have -> : x = l *: x + (1 - l) *: x by rewrite scalerBl addrC subrK scale1r.
  rewrite [X in `|X|](_ : _ = l *: (x - z) + (1 - l) *: (x - y)); last first.
    by rewrite opprD addrACA -mulrBr -mulrBr.
  rewrite (@le_lt_trans _ _ (`|l| * `|x - z| + `|1 - l| * `|x - y|))//.
    by rewrite -!normrM ler_normD.
  rewrite (@lt_le_trans _ _ (`|l| * r + `|1 - l| * r ))//.
    rewrite ltr_leD//.
      by rewrite -ltr_pdivlMl ?mulrA ?mulVf ?mul1r // ?normrE ?gt_eqF.
    by rewrite -ler_pdivlMl ?mulrA ?mulVf ?mul1r ?ltW // ?normrE ?gt_eqF.
  suff-> : `|1 - l| = 1 - `|l| by rewrite -mulrDl addrC subrK mul1r.
  by move: l0 l1 => /ltW/normr_idP -> /ltW/normr_idP ->.
split.
  move=> B [x] [r] ->.
  rewrite openE/= /ball/= /interior => y /= bxy; rewrite -nbhs_ballE.
  exists (r - `|x - y|) => /=; first by rewrite subr_gt0.
  move=> z; rewrite /ball/= ltrBrDr.
  by apply: le_lt_trans; rewrite [in leRHS]addrC ler_distD.
move=> x B; rewrite -nbhs_ballE/= => -[r] r0 Bxr /=.
by exists (ball x r) => //; split; [exists x, r|exact: ballxx].
Qed.

HB.instance Definition _ := Uniform_isTvs.Build R R^o
  standard_add_continuous standard_scale_continuous standard_locally_convex.

End standard_topology.

Section prod_Tvs.
Context (K : numFieldType) (E F : tvsType K).

Local Lemma prod_add_continuous : continuous (fun x : (E * F) * (E * F) => x.1 + x.2).
Proof.
move => [/= xy1 xy2] /= U /= [] [A B] /= [nA nB] nU.
have [/= A0 [A01 A02] nA1] := @add_continuous K E (xy1.1, xy2.1) _ nA.
have [/= B0 [B01 B02] nB1] := @add_continuous K F (xy1.2, xy2.2) _ nB.
exists ([set xy | A0.1 xy.1 /\ B0.1 xy.2], [set xy | A0.2 xy.1 /\ B0.2 xy.2]).
  by split; [exists (A0.1, B0.1)|exists (A0.2, B0.2)].
move => [[x1 y1][x2 y2]] /= [] [] a1 b1 [] a2 b2.
by apply: nU; split; [exact: (nA1 (x1, x2))|exact: (nB1 (y1, y2))].
Qed.

Local Lemma prod_scale_continuous : continuous (fun z : K^o * (E * F) => z.1 *: z.2).
Proof.
move => [/= r [x y]] /= U /= []/= [A B] /= [nA nB] nU.
have [/= A0 [A01 A02] nA1] := @scale_continuous K E (r, x) _ nA.
have [/= B0 [B01 B02] nB1] := @scale_continuous K F (r, y) _ nB .
exists (A0.1 `&` B0.1, A0.2 `*` B0.2).
  by split; [exact: filterI|exists (A0.2,B0.2)].
by move=> [l [e f]] /= [] [Al Bl] [] Ae Be; apply: nU; split;
  [exact: (nA1 (l, e))|exact: (nB1 (l, f))].
Qed.

Local Lemma prod_locally_convex :
  exists2 B : set (set (E * F)), (forall b, b \in B -> convex b) & basis B.
Proof.
have [Be Bcb Beb] := @locally_convex K E.
have [Bf Bcf Bfb] := @locally_convex K F.
pose B := [set ef : set (E * F) | open ef /\
  exists be, exists2 bf, Be be & Bf bf /\ be `*` bf = ef].
have : basis B.
  rewrite /basis/=; split; first by move=> b => [] [].
  move=> /= [x y] ef [[ne nf]] /= [Ne Nf] Nef.
  case: Beb => Beo /(_ x ne Ne) /= -[a] [] Bea ax ea.
  case: Bfb => Bfo /(_ y nf Nf) /= -[b] [] Beb yb fb.
  exists [set z | a z.1 /\ b z.2]; last first.
    by apply: subset_trans Nef => -[zx zy] /= [] /ea + /fb.
  split=> //=; split; last by exists a, b.
  rewrite openE => [[z z'] /= [az bz]]; exists (a, b) => /=; last by [].
  rewrite !nbhsE /=; split; first by exists a => //; split => //; exact: Beo.
  by exists b => //; split => // []; exact: Bfo.
exists B => // => b; rewrite inE /= => [[]] bo [] be [] bf Bee [] Bff <-.
move => [x1 y1] [x2 y2] l /[!inE] /= -[xe1 yf1] [xe2 yf2] l0 l1.
by split; rewrite -inE; [apply: Bcb; rewrite ?inE|apply: Bcf; rewrite ?inE].
Qed.

HB.instance Definition _ :=
  Uniform_isTvs.Build K (E * F)%type
  prod_add_continuous prod_scale_continuous prod_locally_convex.

End prod_Tvs.
