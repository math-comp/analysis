(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum finmap matrix.
From mathcomp Require Import rat interval zmodp vector fieldext falgebra.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality set_interval Rstruct.
Require Import ereal reals signed topology prodnormedzmodule.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

HB.structure Definition PointedNmodule := {M of Pointed M & GRing.Nmodule M}.
HB.structure Definition PointedZmodule := {M of Pointed M & GRing.Zmodule M}.
HB.structure Definition FilteredNmodule := {M of Filtered M M & GRing.Nmodule M}.
HB.structure Definition FilteredZmodule := {M of Filtered M M & GRing.Zmodule M}.
HB.structure Definition NbhsNmodule := {M of Nbhs M & GRing.Nmodule M}.
HB.structure Definition NbhsZmodule := {M of Nbhs M & GRing.Zmodule M}.
HB.structure Definition TopologicalNmodule := {M of Topological M & GRing.Nmodule M}.
HB.structure Definition TopologicalZmodule := {M of Uniform M & GRing.Zmodule M}.

Definition convex (R : ringType) (M : lmodType R) (A : set M) :=
  forall x y lambda, lambda *: x + (1 - lambda) *: y \in A.

HB.mixin Record Uniform_isEvt (R : numDomainType) E of Uniform E & GRing.Lmodule R E := {
  add_continuous : continuous (fun x : E * E => x.1 + x.2) ;
    (*continuous (uncurry (@GRing.add E))*)
  scale_continuous : continuous (fun z : R^o * E => z.1 *: z.2) ;
    (* continuous (uncurry (@GRing.scale R E) : R^o * E -> E) *)
  locally_convex : exists2 B : set (set E), (forall b, b \in B -> convex b) & basis B
}.

#[short(type="evtType")]
HB.structure Definition Evt (R : numDomainType) :=
  {E of Uniform_isEvt R E & Uniform E & GRing.Lmodule R E}.

HB.factory Record TopologicalLmod_isEvt (R : numFieldType) E
    of Topological E & GRing.Lmodule R E := {
  add_continuous : continuous (uncurry (@GRing.add E));
  scale_continuous : continuous (uncurry (@GRing.scale R E) : R^o * E -> E);
  locally_convex : exists2 B : set (set E), (forall b, b \in B -> convex b) & basis B
}.

HB.builders Context R E of TopologicalLmod_isEvt R E.

Definition entourage : set_system (E * E):=
  fun P => exists U, nbhs 0 U /\ (forall xy : E * E, (xy.1 - xy.2) \in U -> xy \in P).

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

Lemma entourage_refl_subproof (A : set (E * E)) :
  entourage A -> [set xy | xy.1 = xy.2] `<=` A.
Proof. (*why bother with \in ?*)
rewrite /entourage => -[/=U [U0 Uxy]] xy //= /eqP; rewrite -subr_eq0 => /eqP xyE.
by rewrite -in_setE; apply: Uxy; rewrite xyE in_setE; apply: nbhs_singleton.
Qed.

Lemma nbhs0N (U : set E) : nbhs 0 U -> nbhs 0 (-%R @` U).
Proof.
move => U0. move: (@scale_continuous ((-1,0)) U); rewrite /= scaler0 => /(_ U0).
move => [] //= [B] B12  [B1 B2] BU.
near=> x; move =>  //=; exists (-x); last by rewrite opprK.
rewrite -scaleN1r; apply: (BU (-1,x)); split => //=; last first.
  by near:x; rewrite nearE.
move: B1 => [] //= ? ?; apply => [] /=;  first by rewrite subrr normr0 //.
Unshelve. all: by end_near. Qed.

Lemma nbhs0_scaler (U : set E) (r : R) : r != 0 -> nbhs 0 U -> nbhs 0 ( *:%R r @` U).
Proof.
move => r0 U0; move: (@scale_continuous ((r^-1,0)) U); rewrite /= scaler0 => /(_ U0).
case=>//= [B] [B1 B2] BU.
near=> x => //=; exists (r^-1*:x); last by rewrite scalerA divrr ?scale1r ?unitfE //=.
apply: (BU (r^-1,x)); split => //=; last by near: x.
by apply: nbhs_singleton.
Unshelve. all: by end_near. Qed.

Lemma nbhs_scaler (U : set E) (r : R) (x :E) :
  r != 0 -> nbhs x U -> nbhs (r *:x) ( *:%R r @` U).
Proof.
move => r0 U0; move: (@scale_continuous ((r^-1,r *:x)) U).
rewrite /= scalerA mulrC divrr ?scale1r ?unitfE //= =>/(_ U0).
case=>//= [B] [B1 B2] BU.
near=> z => //=.
exists (r^-1*:z).
apply: (BU (r^-1,z)); split => //=; last by near: z.
by apply: nbhs_singleton.
by rewrite scalerA divrr ?scale1r ?unitfE //=.
Unshelve. all: by end_near. Qed.

Lemma nbhsT: forall (U : set E), forall (x : E), nbhs 0 U -> nbhs x (+%R x @`U).
Proof.
move => U x U0.
move: (@add_continuous (x,-x) U) => /=; rewrite subrr => /(_ U0) //=.
case=> //= [B] [B1 B2] BU. near=> x0.
exists (x0-x); last by rewrite //= addrCA subrr addr0.
apply: (BU (x0,-x)); split => //=; last by apply: nbhs_singleton.
by near: x0; rewrite nearE.
Unshelve. all: by end_near. Qed.

Lemma nbhs_add: forall (U : set E) (z :E), forall (x : E), nbhs z U -> nbhs (x + z) (+%R x @`U).
Proof.
move => U z x U0. 
move: (@add_continuous ((x+z)%E,-x) U) => /=. rewrite addrAC subrr add0r.
move=> /(_ U0) //=.
case=> //= [B] [B1 B2] BU. near=> x0.
exists (x0-x); last by rewrite //= addrCA subrr addr0.
apply: (BU (x0,-x)); split => //=; last by apply: nbhs_singleton. 
by near: x0; rewrite nearE.  
Unshelve. all: by end_near.
Qed.

Lemma entourage_inv_subproof :
  forall A : set (E * E), entourage A -> entourage A^-1%relation.
Proof.
move => A [/=U [U0 Uxy]]; rewrite /entourage /=.
exists (-%R@`U); split; first by apply: nbhs0N.
move => xy; rewrite in_setE -opprB => [[yx] Uyx] => /oppr_inj H.
by apply: Uxy; rewrite in_setE /= -H.
Qed.

Lemma entourage_split_ex_subproof :
      forall A : set (E * E),
      entourage A -> exists2 B : set (E * E), entourage B & (B \; B)%relation `<=` A.
Proof.
move=> A [/= U] [U0 Uxy]; rewrite /entourage /=.
move: add_continuous. rewrite /continuous_at /==> /(_ (0,0)) /=; rewrite addr0.
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

Lemma nbhsE_subproof : nbhs = nbhs_ entourage.
Proof.
have lem : -1 != 0 :> R by rewrite oppr_eq0 oner_eq0.
rewrite /nbhs_  /=; apply: funext => x; rewrite /filter_from /=.
apply: funext => U; apply: propext => /=; rewrite /entourage /=; split.
  pose V := [set v | (x-v) \in U] : set E.
  move=> nU; exists [set xy |  (xy.1 - xy.2) \in V].
    exists V;split.
      move: (nbhs_add (x) (nbhs_scaler lem nU))=> /=.
      rewrite scaleN1r subrr /= /V.
      have -> : [set (x + x0)%E | x0 in [set -1 *: x | x in U]]
                = [set v | x - v \in U].
       apply: funext => /= v /=; rewrite inE; apply: propext; split.
         by move => [x0 [x1]] Ux1 <- <-; rewrite scaleN1r opprB addrCA subrr addr0.
      move=> Uxy. exists (v - x). exists (x -v) => //.
      by rewrite scaleN1r opprB.
      by rewrite addrCA subrr addr0 //. 
      by [].
    by move=> xy; rewrite !inE=> Vxy; rewrite /= !inE.
  by move=> y /xsectionP; rewrite /V /= !inE /= opprB addrCA subrr addr0 inE.
move=> [A [U0 [NU UA]] H].
near=> z; apply: H => /=; apply/xsectionP; rewrite -inE; apply: UA => /=.
near: z; rewrite nearE.
move: (nbhsT x (nbhs0_scaler lem NU))=> /=.
have -> : 
[set (x + x0)%E | x0 in [set -1 *: x | x in U0]] = (fun x0 : E => x - x0 \in U0).
  apply:funext => /= z /=; apply: propext; split.
    move=> [x0] [x1 Ux1 <-] <-.
    rewrite  -opprB. rewrite addrAC subrr add0r inE scaleN1r opprK //.
   rewrite inE => Uxz. exists (z-x). exists (x-z) => //.
   by rewrite scalerBr !scaleN1r opprK addrC. 
   by rewrite addrCA subrr addr0.
by [].
Unshelve. all: by end_near.
Qed.

HB.instance Definition _ := Nbhs_isUniform_mixin.Build E
    entourage_filter entourage_refl_subproof
    entourage_inv_subproof entourage_split_ex_subproof
    nbhsE_subproof.
HB.end.

Definition dual {R : ringType} (E : lmodType R) : Type := {scalar E}.
(* Check fun {R : ringType} (E : lmodType R) => dual E : ringType. *)

HB.mixin Record hasDual (R : ringType) (E' : lmodType R) E of GRing.Lmodule R E :=  {
 dual_pair : E -> E' -> R;
 dual_pair_rlinear : forall x, scalar (dual_pair x);
 dual_pair_llinear : forall x, scalar (dual_pair^~ x);
 ipair : injective ( fun x =>  dual_pair^~ x)
}.

Section bacasable.

Lemma add_continuousE (R : numDomainType) (E : evtType R) :
  continuous (fun xy : E * E => xy.1 + xy.2).
Proof.
apply: add_continuous.
Qed.

End bacasable.
