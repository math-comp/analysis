(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.  *)  
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum finmap matrix.
From mathcomp Require Import rat interval zmodp vector fieldext falgebra.
From mathcomp Require Import archimedean.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import cardinality set_interval.
Require Import ereal reals signed topology prodnormedzmodule function_spaces.
Require Export separation_axioms.

(**md**************************************************************************)
(*                                                                            *)
(* This file introduces locally convex topological vector spaces              *)
(*                                                                            *)
(* ## Topological vector spaces                                               *)
(* ```                                                                        *)
(*             tvsType R  == interface type for a locally convex topological  *)
(*                           vector space on a numDomain R. A tvs is          *)
(*                           constructed over a uniform space                 *)
(*  TopologicalLmod_isTvs == factory allowing the construction of a tvs from  *)
(*                           a lmodule which is also a topological space.     *)
(*  ```                                                                       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

HB.structure Definition PointedNmodule := {M of Pointed M & GRing.Nmodule M}.
HB.structure Definition PointedZmodule := {M of Pointed M & GRing.Zmodule M}.
HB.structure Definition PointedLmodule (K : numDomainType) := {M of Pointed M & GRing.Lmodule K M}.

HB.structure Definition FilteredNmodule := {M of Filtered M M & GRing.Nmodule M}.
HB.structure Definition FilteredZmodule := {M of Filtered M M & GRing.Zmodule M}.
HB.structure Definition FilteredLmodule (K : numDomainType) :=
  {M of Filtered M M & GRing.Lmodule K M}.
HB.structure Definition NbhsNmodule := {M of Nbhs M & GRing.Nmodule M}.
HB.structure Definition NbhsZmodule := {M of Nbhs M & GRing.Zmodule M}.
HB.structure Definition NbhsLmodule (K : numDomainType) :=
  {M of Nbhs M & GRing.Lmodule K M}.

(*HB.structure Definition TopologicalNmodule := {M of Topological M & GRing.Nmodule M}.*)
HB.structure Definition TopologicalZmodule :=
  {M of Topological M & GRing.Zmodule M}.
HB.structure Definition TopologicalLmodule (K : numDomainType) :=
  {M of Topological M & GRing.Lmodule K M}.
HB.structure Definition UniformZmodule := {M of Uniform M & GRing.Zmodule M}.
HB.structure Definition UniformLmodule (K : numDomainType) :=
  {M of Uniform M & GRing.Lmodule K M}.

Definition convex (R : numDomainType) (M : lmodType R) (A : set M) :=
  forall x y (lambda : R), x \in A -> y \in A ->
  (0< lambda) -> (lambda < 1) -> lambda *: x + (1 - lambda) *: y \in A.


HB.mixin Record Uniform_isTvs (R : numDomainType) E of Uniform E & GRing.Lmodule R E := {
  add_continuous : continuous (fun x : E * E => x.1 + x.2) ;
  scale_continuous : continuous (fun z : R^o * E => z.1 *: z.2) ;
  locally_convex : exists2 B : set (set E), (forall b, b \in B -> convex b) & basis B;
}.

#[short(type="tvsType")]
HB.structure Definition Tvs (R : numDomainType) :=
  {E of Uniform_isTvs R E & Uniform E & GRing.Lmodule R E}.

Section properties_of_topologicallmodule.
Context (R : numDomainType) (E : TopologicalLmodule.type R) (U : set E).

Lemma nbhsN_subproof (f : continuous (fun z : R^o * E => z.1 *: z.2)) (x : E) :
  nbhs x U -> nbhs (-x) (-%R @` U).
Proof.
move => Ux; move: (@f (-1,-x) U); rewrite /= scaleN1r opprK => /(_ Ux) [] /=.
move => [B] B12  [B1 B2] BU; near=> y; exists (-y); rewrite ?opprK -?scaleN1r //.
apply: (BU (-1,y)); split => /=; last by near:y; rewrite nearE.
by move: B1 => [] //= ? ?; apply => [] /=; rewrite subrr normr0.
Unshelve. all: by end_near. Qed.

Lemma nbhs0N_subproof (f : continuous (fun z : R^o * E => z.1 *: z.2 : E)) :
  nbhs 0 U -> nbhs 0 (-%R @` U).
Proof.
by move => Ux; rewrite -oppr0; apply: nbhsN_subproof.
Qed.

Lemma nbhsT_subproof (f : continuous (fun x : E * E => x.1 + x.2)) (x : E) :
  nbhs 0 U -> nbhs x (+%R x @`U).
Proof.
move => U0; move: (@f (x,-x) U) => /=; rewrite subrr => /(_ U0) //=.
case=> //= [B] [B1 B2] BU; near=> x0.
exists (x0-x); last by rewrite //= addrCA subrr addr0.
apply: (BU (x0,-x)); split => //=; last by apply: nbhs_singleton.
by near: x0; rewrite nearE.
Unshelve. all: by end_near. Qed.

Lemma nbhsB_subproof (f : continuous (fun x : E * E => x.1 + x.2)) (z x : E) :
  nbhs z U -> nbhs (x + z) (+%R x @`U).
Proof.
move => U0; move: (@f ((x+z)%E,-x) U); rewrite /= addrAC subrr add0r.
move=> /(_ U0) //=; case=> //= [B] [B1 B2] BU;  near=> x0.
exists (x0-x); last by rewrite //= addrCA subrr addr0.
apply: (BU (x0,-x)); split => //=; last by apply: nbhs_singleton.
by near: x0; rewrite nearE.
Unshelve. all: by end_near.
Qed.

End properties_of_topologicallmodule.

HB.factory Record TopologicalLmod_isTvs (R : numDomainType) E
    of Topological E & GRing.Lmodule R E := {
  add_continuous : continuous (fun x : E * E => x.1 + x.2) ;
    (*continuous (uncurry (@GRing.add E))*)
  scale_continuous : continuous (fun z : R^o * E => z.1 *: z.2) ;
    (* continuous (uncurry (@GRing.scale R E) : R^o * E -> E) *)
  locally_convex : exists2 B : set (set E), (forall b, b \in B -> convex b) & basis B
  }.

HB.builders Context R E of TopologicalLmod_isTvs R E.

Definition entourage : set_system (E * E):=
  fun P => exists U, nbhs 0 U /\ (forall xy : E * E, (xy.1 - xy.2) \in U -> xy \in P).

(* TODO: delete the next lemmas to better incorporate their proofs*)
Let nbhs0N (U : set E) : nbhs 0 U -> nbhs 0 (-%R @` U).
Proof. by apply: nbhs0N_subproof; exact: scale_continuous. Qed.

Lemma nbhsN (U : set E) (x : E) : nbhs x U -> nbhs (-x) (-%R @` U).
Proof.
by apply: nbhsN_subproof; exact: scale_continuous.
Qed.

Let nbhsT (U : set E) (x : E) : nbhs 0 U -> nbhs x (+%R x @`U).
Proof. by apply: nbhsT_subproof; exact: add_continuous. Qed.

Let nbhsB (U : set E) (z x : E) : nbhs z U -> nbhs (x + z) (+%R x @`U).
Proof. by apply: nbhsB_subproof; exact: add_continuous. Qed.

Lemma entourage_filter : Filter entourage.
Proof.
split.
- exists [set: E]; split; first by apply: filter_nbhsT.
  by move => xy //=.
- move => P Q; rewrite /entourage nbhsE //=.
  move => [U [[B B0] BU Bxy]]  [V [[C C0] CV Cxy]].
  exists (U`&`V); split.
    exists (B`&`C); first by apply/open_nbhsI.
    by apply:setISS.
  move => xy; rewrite !in_setI.
  move/andP => [xyU xyV]; apply/andP;split; first by apply:Bxy.
  by apply: Cxy.
move => P Q PQ; rewrite /entourage /= => [[U [HU Hxy]]]; exists U; split => //.
by move => xy /Hxy /[!inE] /PQ.
Qed.

Local Lemma entourage_refl (A : set (E * E)) :
  entourage A -> [set xy | xy.1 = xy.2] `<=` A.
Proof.
rewrite /entourage => -[/=U [U0 Uxy]] xy //= /eqP; rewrite -subr_eq0 => /eqP xyE.
by rewrite -in_setE; apply: Uxy; rewrite xyE in_setE; apply: nbhs_singleton.
Qed.

Local Lemma entourage_inv :
  forall A : set (E * E), entourage A -> entourage A^-1%relation.
Proof.
move => A [/=U [U0 Uxy]]; rewrite /entourage /=.
exists (-%R@`U); split; first exact: nbhs0N.
move => xy; rewrite in_setE -opprB => [[yx] Uyx] => /oppr_inj H.
by apply: Uxy; rewrite in_setE /= -H.
Qed.

Local Lemma entourage_split_ex :
      forall A : set (E * E),
      entourage A -> exists2 B : set (E * E), entourage B & (B \; B)%relation `<=` A.
Proof.
move=> A [/= U] [U0 Uxy]; rewrite /entourage /=.
move: add_continuous; rewrite /continuous_at /==> /(_ (0,0)) /=; rewrite addr0.
move=> /(_ U U0) [] /= [W1 W2] []; rewrite nbhsE /==> [[U1 nU1 UW1] [U2 nU2 UW2]] Wadd.
exists ([set w |(W1 `&` W2)  (w.1 - w.2) ]).
  exists (W1 `&` W2); split; last by [].
  exists (U1 `&` U2); first by apply: open_nbhsI.
  move => t [U1t U2t]; split; first by apply: UW1.
  by apply: UW2.
move => xy /= [z [H _] [_ H']]; rewrite -inE; apply: (Uxy xy); rewrite inE.
have -> : xy.1 - xy.2= (xy.1 - z) + (z - xy.2).
  by rewrite addrA -[X in (_ = X + _)]addrA [X in (_ = (_ + X)+_)]addrC addrN addr0.
by apply: (Wadd( (xy.1 - z,z - xy.2))); split => //=.
Qed.

Local Lemma nbhsE : nbhs = nbhs_ entourage.
Proof.
have lem : -1 != 0 :> R by rewrite oppr_eq0 oner_eq0.
rewrite /nbhs_  /=; apply: funext => x; rewrite /filter_from /=.
apply: funext => U; apply: propext => /=; rewrite /entourage /=; split.
  pose V := [set v | (x-v) \in U] : set E.
  move=> nU; exists [set xy |  (xy.1 - xy.2) \in V]. 
  exists V;split => //=.
      move: (nbhsB (x) (nbhsN nU)); rewrite /= subrr /= /V.
      have -> // : [set (x + x0)%E | x0 in [set - x | x in U]]
                = [set v | x - v \in U].
         apply: funext => /= v /=; rewrite inE; apply: propext; split.
         by move => [x0 [x1]] Ux1 <- <-; rewrite  opprB addrCA subrr addr0.
       move=> Uxy; exists (v - x) => //; last by rewrite addrCA subrr addr0.
       by exists (x -v) => //; rewrite opprB. 
  by move=> xy; rewrite !inE=> Vxy; rewrite /= !inE.
  by move=> y /xsectionP; rewrite /V /= !inE /= opprB addrCA subrr addr0 inE.
move=> [A [U0 [nU UA]] H]; near=> z; apply: H => /=; apply/xsectionP; rewrite -inE; apply: UA => /=.
near: z; rewrite nearE; move: (nbhsT x (nbhs0N nU))=> /=.
suff -> : 
[set (x + x0)%E | x0 in [set - x | x in U0]] = (fun x0 : E => x - x0 \in U0) by [].
apply:funext => /= z /=; apply: propext; split.
   move=> [x0] [x1 Ux1 <-] <-; rewrite -opprB addrAC subrr add0r inE opprK //.
   rewrite inE => Uxz; exists (z-x); last by rewrite addrCA subrr addr0.
   by exists (x-z); rewrite ?opprB.
Unshelve. all: by end_near.
Qed.

HB.instance Definition _ := Nbhs_isUniform_mixin.Build E
    entourage_filter entourage_refl
    entourage_inv entourage_split_ex
    nbhsE.
HB.end.

Section Tvs_numDomain.

Context (R : numDomainType) (E : tvsType R) (U : set E).

Lemma nbhs0N : nbhs 0 U -> nbhs 0 (-%R @` U).
Proof. by apply: nbhs0N_subproof; exact: scale_continuous. Qed.

Lemma nbhsT (x :E) : nbhs 0 U -> nbhs x (+%R x @`U).
Proof. by apply: nbhsT_subproof; exact: add_continuous. Qed.

Lemma nbhsB (z x : E) : nbhs z U -> nbhs (x + z) (+%R x @`U).
Proof. by apply: nbhsB_subproof; exact: add_continuous. Qed.

End Tvs_numDomain.

Section Tvs_numField.

Lemma nbhs0Z  (R : numFieldType) (E : tvsType R) (U : set E) (r : R) :
  r != 0 -> nbhs 0 U -> nbhs 0 ( *:%R r @` U).
Proof.
move => r0 U0; move: (scale_continuous ((r^-1,0)) U); rewrite /= scaler0 => /(_ U0).
case=>//= [B] [B1 B2] BU.
near=> x => //=; exists (r^-1*:x); last by rewrite scalerA divrr ?scale1r ?unitfE //=.
apply: (BU (r^-1,x)); split => //=; last by near: x.
by apply: nbhs_singleton.
Unshelve. all: by end_near. Qed.

Lemma nbhsZ  (R : numFieldType) (E : tvsType R) (U : set E) (r : R) (x :E) :
  r != 0 -> nbhs x U -> nbhs (r *:x) ( *:%R r @` U).
Proof.
move => r0 U0; move: (scale_continuous ((r^-1,r *:x)) U).
rewrite /= scalerA mulrC divrr ?scale1r ?unitfE //= =>/(_ U0).
case=>//= [B] [B1 B2] BU.
near=> z => //=.
exists (r^-1*:z).
apply: (BU (r^-1,z)); split => //=; last by near: z.
by apply: nbhs_singleton.
by rewrite scalerA divrr ?scale1r ?unitfE //=.
Unshelve. all: by end_near. Qed.

End Tvs_numField.

Section standard_topology.
Variable R : numFieldType.

Lemma standard_add_continuous : continuous (fun x : R^o * R^o => x.1 + x.2).
Proof.
(* NB(rei): almost the same code as in normedtype.v *)
move=> [/= x y]; apply/cvg_ballP => e e0 /=.
exists (ball x (e / 2), ball y (e / 2)) => /=.
  by split; apply: nbhsx_ballx; rewrite divr_gt0.
rewrite /ball /ball_/= => xy /= [nx ny].
by rewrite opprD addrACA (le_lt_trans (ler_normD _ _)) // (splitr e) ltrD.
Qed.

Lemma standard_scale_continuous : continuous (fun z : R^o * R^o => z.1 *: z.2).
Proof.
(* NB: This lemma is proved once again in normedtype, in a shorter way with much more machinery *)
(*     To be rewritten once normedtype is split and tvs can depend on these lemmas *)
move=> [k x]; apply/cvg_ballP => e le0 /=.
pose M : R := maxr (`|e| + 1) (maxr `|k| (`|x| + `|x| + 2^-1 + 1)).
have M0l : 0 < `|e| + 1 by rewrite ltr_wpDl.
have M0r : 0 < maxr `|k| (`|x| + `|x| + 2^-1 + 1).
  rewrite /maxr; case: ifPn => //.
  have [->|k0 _] := eqVneq k 0; last by rewrite normr_gt0.
  rewrite normr0 -ltrBlDr sub0r ltxx => /negbTE <-.
  by rewrite (lt_le_trans (@ltrN10 _)).
have M0 : 0 < M.
  by have /= -> := num_lt_max 0 (PosNum M0l) (PosNum M0r); rewrite M0l.
have Me : `|e| < M.
  rewrite (@lt_le_trans _ _ (`|e| + 1)) ?ltrDl//.
  have /= -> := num_le_max (`|e| + 1) (PosNum M0l) (PosNum M0r).
  by rewrite lexx.
pose r := `|e| / 2 / M.
exists (ball k r, ball x r).
  by split; exists r => //=; rewrite !divr_gt0// normr_gt0 gt_eqF.
move=> /= [z1 z2] [k1r k2r].
have := @ball_split _ _ (k * z2)  (k * x)  (z1 * z2) `|e|.
rewrite /ball /= /= real_lter_normr ?gtr0_real//.
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

Lemma standard_locally_convex :
  exists2 B : set (set R^o), (forall b, b \in B -> convex b) & basis B.
Proof.
(* NB(rei): almost the same code as in normedtype.v *)
exists [set B | exists x r, B = ball x r].
  move=> b; rewrite inE /= => [[x]] [r] -> z y l.
  rewrite !inE /ball /= => zx yx l0; rewrite -subr_gt0 => l1.
  have -> : x = l *: x + (1 - l) *: x.
    by rewrite scalerBl addrCA subrr addr0 scale1r.
  rewrite [X in `|X|](_ : _ = l *: (x - z) + (1 - l) *: (x - y)); last first.
    by rewrite opprD addrACA -mulrBr -mulrBr.
  rewrite (@le_lt_trans _ _ (`|l| * `|x - z| + `|1 - l| * `|x - y|))//.
    by rewrite -!normrM ler_normD.
  rewrite (@lt_le_trans _ _ (`|l| * r + `|1 - l| * r ))//.
    rewrite ltr_leD//.
      by rewrite -ltr_pdivlMl ?mulrA ?mulVf ?mul1r // ?normrE ?gt_eqF.
    by rewrite -ler_pdivlMl ?mulrA ?mulVf ?mul1r ?ltW // ?normrE ?gt_eqF.
  have -> : `|1 - l| = 1 - `| l |.
    by move: l0 l1 => /ltW/normr_idP -> /ltW/normr_idP ->.
  by rewrite -mulrDl addrCA subrr addr0 mul1r.
split.
  move=> B [x] [r] ->.
  rewrite openE/= /ball/= /interior => y /= bxy; rewrite -nbhs_ballE.
  exists (r - `|x - y|) => /=; first by rewrite subr_gt0.
  move=> z; rewrite /ball/= ltrBrDr.
  by apply: le_lt_trans; rewrite [in leRHS]addrC ler_distD.
move=> x B; rewrite -nbhs_ballE/= => -[r] r0 Bxr /=.
by exists (ball x r) => //; split; [exists x, r|exact: ballxx].
Qed.

HB.instance Definition _ := Uniform_isTvs.Build R (R^o)%type
  standard_add_continuous standard_scale_continuous standard_locally_convex.

End standard_topology.

Section prod_Tvs.
Context (K : numFieldType) (E F : tvsType K).

Lemma prod_add_continuous : continuous (fun x : (E * F) * (E * F) => x.1 + x.2).
Proof.
move => [/= xy1 xy2] /= U /= [] [A B] /= [nA nB] nU.
rewrite nbhs_simpl /=.
move: (@add_continuous K E (xy1.1,xy2.1) _ nA); rewrite nbhs_simpl /= => [[]] /= A0 [A01 A02] nA1.
move: (@add_continuous K F (xy1.2,xy2.2) _ nB); rewrite nbhs_simpl /= => [[]] /= B0 [B01 B02] nB1.
exists ([set xy : (E*F) |( A0.1 xy.1) /\ (B0.1 xy.2) ], [set xy : (E*F) |( A0.2 xy.1) /\ (B0.2 xy.2) ]) => //=.
  split; first by exists (A0.1,B0.1).
  by exists (A0.2,B0.2).
move => [[x1 y1][x2 y2]] /= [] [] a1 b1 [] a2 b2.
apply: nU; split => /=; first by move : (nA1 (x1,x2)) => /=; apply.
by move : (nB1 (y1,y2)) => /=; apply.
Qed.

Lemma prod_scale_continuous : continuous (fun z : K^o * (E * F) => z.1 *: z.2).
Proof.
move => [/= r [x y]] /= U /= []/= [A B] /= [nA nB] nU. 
rewrite nbhs_simpl /=.
move: (@scale_continuous K E (r,x) _ nA); rewrite nbhs_simpl /= => [[]] /= A0 [A01 A02] nA1.
move: (@scale_continuous K F (r,y) _ nB); rewrite nbhs_simpl /= => [[]] /= B0 [B01 B02] nB1.
exists (A0.1 `&` B0.1,(A0.2 `*` B0.2)) => /=. 
  split=> /=. apply: filterI => //.
exists (A0.2,B0.2); first by split => //=.
  by [].  
move=> [l [e f]] /= [] [Al Bl] [] Ae Be; apply: nU => /=; split.
  by move : (nA1 (l,e)) => /=;  apply.
  by move : (nB1 (l,f)) => /=; apply.
Qed.

Lemma prod_locally_convex : 
exists2 B : set (set (E * F)), (forall b, b \in B -> convex b) & basis B.
Proof.
move: (@locally_convex K E)=> [Be Bcb Beb].
move: (@locally_convex K F)=> [Bf Bcf Bfb].
pose B:=  [set ef : set (E*F) | open ef /\
     (exists be, exists2 bf, (Be be) & (( Bf bf)/\ (be `*` bf = ef)))].
exists B.
  move=> b; rewrite inE /= => [[]] bo [] be [] bf Bee [] Bff <-.  
  move => [x1 y1] [x2 y2] l; rewrite !inE =>- /= [xe1 yf1] [xe2 yf2] l0 l1.
  split; rewrite -inE; first by apply: Bcb; rewrite ?inE.
  by apply: Bcf; rewrite ?inE.
rewrite /basis /=.
split; first  by move=> b /= => [] [].
move => /= [x y]; rewrite /filter_from /nbhs_simpl => ef [[ne nf]] /= [Ne Nf] Nef.
rewrite nbhs_simpl /=. 
move: Beb=> [] Beo /(_ x ne Ne) /=; rewrite !nbhs_simpl /= =>- [a] [] Bea ax ea.
move: Bfb=> [] Bfo /(_ y nf Nf) /=; rewrite !nbhs_simpl /= =>- [b] [] Beb yb fb.
exists [set z | (a z.1) /\ (b z.2)]; last first.
  apply: subset_trans; last by apply:Nef.
  by move=> [zx zy] /= [] /ea + /fb. 
split => /=; last by split; rewrite /B /=.   
split; last by exists a; exists b; rewrite ?inE //.  
rewrite openE => [[z z'] /= [az bz]]; exists (a,b) => /=; last by [].
rewrite !nbhsE /=; split; first by  exists a => //; split => //; apply: Beo.
by exists b =>  //; split =>  // []; apply: Bfo.
Qed.

HB.instance Definition _ :=
  Uniform_isTvs.Build K (E * F)%type
  prod_add_continuous prod_scale_continuous prod_locally_convex.

End prod_Tvs.
