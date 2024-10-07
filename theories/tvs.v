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


Definition convex_hull  (R : numDomainType) (M : lmodType R) (A : set M) :=
  [set z | exists2 l : R,(0 < l /\ (l < 1))&(exists2 x, (x \in A) &
(exists2 y, (y \in A)&(z = (l *: x + (1 - l) *: y))))].

Lemma convex_convexhull (R : numDomainType) (M : lmodType R) (A : set M) :
  convex (convex_hull A).
Proof.
  move => x y l; rewrite !inE /convex_hull /= =>- [lx [lx0 lx1] [x1 x1a] [x2 x2a]] xc.
  move => >- [ly [ly0 ly1] [y1 y1a] [y2 y2a]] yc l0 l1.
Admitted.

HB.mixin Record Uniform_isTvs (R : numDomainType) E of Uniform E & GRing.Lmodule R E := {
  add_continuous : continuous (fun x : E * E => x.1 + x.2) ;
    (*continuous (uncurry (@GRing.add E))*)
  scale_continuous : continuous (fun z : R^o * E => z.1 *: z.2) ;
    (* continuous (uncurry (@GRing.scale R E) : R^o * E -> E) *)
  locally_convex : exists2 B : set (set E), (forall b, b \in B -> convex b) & basis B
}.

#[short(type="tvsType")]
HB.structure Definition Tvs (R : numDomainType) :=
  {E of Uniform_isTvs R E & Uniform E & GRing.Lmodule R E}.

Section properties_of_topologicallmodule.
Context (R : numDomainType) (E : TopologicalLmodule.type R) (U : set E).

Lemma nbhs0N_subproof (f : continuous (fun z : R^o * E => z.1 *: z.2 : E)) :
  nbhs 0 U -> nbhs 0 (-%R @` U).
Proof.
move=> U0; have /= := @f (-1, 0) U; rewrite scaler0 => /(_ U0).
move=> [] /= [B] B12  [B1 B2] BU.
near=> x => /=; exists (- x); last by rewrite opprK.
rewrite -scaleN1r; apply: (BU (-1, x)); split => //=; last first.
  by near:x; rewrite nearE.
by move: B1 => [] //= ? ?; apply => [] /=; rewrite subrr normr0.
Unshelve. all: by end_near. Qed.

Lemma nbhsT_subproof (f : continuous (fun x : E * E => x.1 + x.2)) (x : E) :
  nbhs 0 U -> nbhs x (+%R x @`U).
Proof.
move => U0; move: (@f (x,-x) U) => /=; rewrite subrr => /(_ U0) //=.
case=> //= [B] [B1 B2] BU; near=> x0.
exists (x0-x); last by rewrite //= addrCA subrr addr0.
apply: (BU (x0,-x)); split => //=; last by apply: nbhs_singleton.
by near: x0; rewrite nearE.
Unshelve. all: by end_near. Qed.

Lemma nbhs_add_subproof (f : continuous (fun x : E * E => x.1 + x.2)) (z x : E) :
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
move => Ux.
move: (@scale_continuous (-1,-x) U).
rewrite /= scaleN1r opprK => /(_ Ux).
move => [] //= [B] B12  [B1 B2] BU.
near=> y; move =>  //=; exists (-y); last by rewrite opprK.
rewrite -scaleN1r; apply: (BU (-1,y)); split => //=; last first.
  by near:y; rewrite nearE.
move: B1 => [] //= ? ?; apply => [] /=;  first by rewrite subrr normr0 //.
Unshelve. all: by end_near. Qed.

Let nbhsT (U : set E) (x : E) : nbhs 0 U -> nbhs x (+%R x @`U).
Proof. by apply: nbhsT_subproof; exact: add_continuous. Qed.

Let nbhs_add (U : set E) (z x : E) : nbhs z U -> nbhs (x + z) (+%R x @`U).
Proof. by apply: nbhs_add_subproof; exact: add_continuous. Qed.

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

Lemma entourage_inv_subproof :
  forall A : set (E * E), entourage A -> entourage A^-1%relation.
Proof.
move => A [/=U [U0 Uxy]]; rewrite /entourage /=.
exists (-%R@`U); split; first exact: nbhs0N.
move => xy; rewrite in_setE -opprB => [[yx] Uyx] => /oppr_inj H.
by apply: Uxy; rewrite in_setE /= -H.
Qed.

Lemma entourage_split_ex_subproof :
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

Lemma nbhsE_subproof : nbhs = nbhs_ entourage.
Proof.
have lem : -1 != 0 :> R by rewrite oppr_eq0 oner_eq0.
rewrite /nbhs_  /=; apply: funext => x; rewrite /filter_from /=.
apply: funext => U; apply: propext => /=; rewrite /entourage /=; split.
  pose V := [set v | (x-v) \in U] : set E.
  move=> nU; exists [set xy |  (xy.1 - xy.2) \in V]. 
  exists V;split => //=.
      move: (nbhs_add (x) (nbhsN nU)); rewrite /= subrr /= /V.
      have -> : [set (x + x0)%E | x0 in [set - x | x in U]]
                = [set v | x - v \in U].
         apply: funext => /= v /=; rewrite inE; apply: propext; split.
         by move => [x0 [x1]] Ux1 <- <-; rewrite  opprB addrCA subrr addr0.
      move=> Uxy. exists (v - x). exists (x -v) => //. 
      by rewrite opprB.
      by rewrite addrCA subrr addr0 //. 
      by [].
    by move=> xy; rewrite !inE=> Vxy; rewrite /= !inE.
  by move=> y /xsectionP; rewrite /V /= !inE /= opprB addrCA subrr addr0 inE.
move=> [A [U0 [nU UA]] H].
near=> z; apply: H => /=; apply/xsectionP; rewrite -inE; apply: UA => /=.
near: z; rewrite nearE.
move: (nbhsT x (nbhs0N nU))=> /=.
have -> : 
[set (x + x0)%E | x0 in [set - x | x in U0]] = (fun x0 : E => x - x0 \in U0).
  apply:funext => /= z /=; apply: propext; split.
    move=> [x0] [x1 Ux1 <-] <-.
    rewrite  -opprB; rewrite addrAC subrr add0r inE opprK //.
   rewrite inE => Uxz. exists (z-x). exists (x-z) => //.
   by rewrite opprB.
   by rewrite addrCA subrr addr0.
by [].
Unshelve. all: by end_near.
Qed.

HB.instance Definition _ := Nbhs_isUniform_mixin.Build E
    entourage_filter entourage_refl_subproof
    entourage_inv_subproof entourage_split_ex_subproof
    nbhsE_subproof.
HB.end.



Section Tvs_numDomain.
Context (R : numDomainType) (E : tvsType R) (U : set E).

Lemma nbhs0N : nbhs 0 U -> nbhs 0 (-%R @` U).
Proof. by apply: nbhs0N_subproof; exact: scale_continuous. Qed.

Lemma nbhsT (x :E) : nbhs 0 U -> nbhs x (+%R x @`U).
Proof. by apply: nbhsT_subproof; exact: add_continuous. Qed.

Lemma nbhs_add (z x : E) : nbhs z U -> nbhs (x + z) (+%R x @`U).
Proof. by apply: nbhs_add_subproof; exact: add_continuous. Qed.

End Tvs_numDomain.

Section Tvs_numField.

Lemma nbhs0_scaler  (R : numFieldType) (E : tvsType R) (U : set E) (r : R) :
  r != 0 -> nbhs 0 U -> nbhs 0 ( *:%R r @` U).
Proof.
move => r0 U0; move: (scale_continuous ((r^-1,0)) U); rewrite /= scaler0 => /(_ U0).
case=>//= [B] [B1 B2] BU.
near=> x => //=; exists (r^-1*:x); last by rewrite scalerA divrr ?scale1r ?unitfE //=.
apply: (BU (r^-1,x)); split => //=; last by near: x.
by apply: nbhs_singleton.
Unshelve. all: by end_near. Qed.

Lemma nbhs_scaler  (R : numFieldType) (E : tvsType R) (U : set E) (r : R) (x :E) :
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

Section regular_topology.
Variable R : numFieldType.
HB.instance Definition _ := Num.NormedZmodule.on R^o.

Lemma regular_add_continuous : continuous (fun x : R^o * R^o => x.1 + x.2).
Proof.
(* NB(rei): this duplicates code that is also in normedtype.v *)
move=> [/= x y]; apply/cvg_ballP => e e0 /=.
rewrite nearE /= -nbhs_ballE  /nbhs_ball /nbhs_ball_ //=.
exists ((ball x (e/2)),(ball y (e/2))).
rewrite !nbhs_simpl /=; split; by apply: nbhsx_ballx; rewrite ?divr_gt0.
rewrite /ball_ /= => xy /= [nx ny].
by rewrite /ball/= opprD addrACA (le_lt_trans (ler_normD _ _)) // (@splitr R e) ltrD //=.
Qed.

Lemma regular_scale_continuous : continuous (fun z : R^o * R^o => z.1 *: z.2).
Proof.
(* NB(rei): cannot really copy-paste the proof from normedtype.v because it relies on pinfty_nbhs defined in normedtype.v *)
  Admitted.
Lemma regular_locally_convex :
  exists2 B : set (set R^o), (forall b, b \in B -> convex b) & basis B.
Proof.
(* NB(rei): cannot really copy-paste the proof from normedtype.v because it relies on normrZ defined in normedtype.v *)
  Admitted.

HB.instance Definition _ :=
  Uniform_isTvs.Build R (R^o)%type
regular_add_continuous regular_scale_continuous regular_locally_convex.
End regular_topology.

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

Definition dual {R : ringType} (E : lmodType R) : Type := {scalar E}.
(* Check fun {R : ringType} (E : lmodType R) => dual E : ringType. *)

HB.mixin Record hasDual (R : ringType) (E' : lmodType R) E of GRing.Lmodule R E :=  {
 dual_pair : E -> E' -> R;
 dual_pair_rlinear : forall x, scalar (dual_pair x);
 dual_pair_llinear : forall x, scalar (dual_pair^~ x);
 ipair : injective ( fun x =>  dual_pair^~ x)
}.



Section bacasable.

Lemma add_continuousE (R : numDomainType) (E : tvsType R) :
  continuous (fun xy : E * E => xy.1 + xy.2).
Proof.
apply: add_continuous.
Qed.

End bacasable.

About opprB.
