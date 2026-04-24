From HB Require Import structures. 
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import interval_inference.
From mathcomp Require Import unstable wochoice boolp classical_sets topology reals.
From mathcomp Require Import filter reals normedtype convex.
Import numFieldNormedType.Exports.
Local Open Scope classical_set_scope. 

(**md**************************************************************************)
(* # The Hahn-Banach theorem                                                  *)
(*                                                                            *)
(* This files proves the Hahn-Banach theorem thanks to Zorn's lemma. Theorem  *)
(* `Hahnbanach` states that, considering `V` an lmodtype on a realtype, a     *)
(* linear function on a subLmodype of V, that is bounded by a convex          *)
(* function, can be extended to a linear map on V boundeby the same convex    *)
(* function.  Theorem `HB_geom_normed` specifies this to the extention of a   *)
(* linear continuous function on a subspace to the whole NormedModule.        *)
(*                                                                            *)
(* ```                                                                        *)
(*        Module Lingraph == definitions on linear relations, thought of as   *)
(*                           graph of functions                               *)
(*   Module HBPreparation == defintion of the type Zorntype of linear         *)
(*                           functional graphs, bounded by a convex function  *)
(*                           and extending to the whole space a given linear  *)
(*                           graph.                                           *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.
Local Open Scope convex_scope.
Local Open Scope real_scope.
Import GRing.Theory.
Import Num.Theory.

Section pos_quotient.

(* auxiliary lemmas that could be moved elsewhere *)

(* NB: to appear in MathComp 2.6.0 *)
Lemma divDl_ge0 (R: numDomainType) (s t : R) (s0 : 0 <= s) (t0 : 0 <= t) : 0 <= s / (s + t).
Proof.
by apply: divr_ge0 => //; apply: addr_ge0.
Qed.

(* NB: to appear in MathComp 2.6.0 *)
Lemma divDl_le1 (R: numFieldType) (s t : R) (s0 : 0 <= s) (t0 : 0 <= t) :  s / (s + t) <= 1.
Proof.
move: s0; rewrite le0r => /predU1P [->|s0]; first by rewrite mul0r.
by rewrite ler_pdivrMr ?mul1r ?lerDl // ltr_wpDr.
Qed.

Lemma divD_onem (R: realType) (s t : R) (s0 : 0 < s) (t0 : 0 < t) :
  (s / (s + t)).~ = t / (s + t).
Proof.
rewrite /onem.
by rewrite -(@divff _ (s + t)) ?gt_eqF ?addr_gt0// -mulrBl (addrC s) addrK.
Qed.

End pos_quotient.

HB.mixin Record Zmodule_isSubNormed (R : numDomainType)
    (M : normedZmodType R) (S : pred M) T & SubChoice M S T
    & Num.NormedZmodule R T := {
  norm_valE : forall x , @Num.norm _ M ((val : T -> M) x) = @Num.norm _ T x
}.

(* TODO: should go to MathComp in numdomain.v *)
#[short(type="subNormedZmodType")]
HB.structure Definition SubNormedZmodule (R : numDomainType)
    (V : normedZmodType R) (S : pred V) :=
  { U of SubChoice V S U & Num.NormedZmodule R U & GRing.SubZmodule V S U
    & Zmodule_isSubNormed R V S U }.

HB.mixin Record isSubNbhs
  (V : nbhsType) (S : pred V) U & SubChoice V S U & Nbhs U := {
  continuous_valE : continuous (val : U -> V)
}.

#[short(type="subNbhsType")]
HB.structure Definition SubNbhs (V : nbhsType) (S : pred V) :=
  { U of SubChoice V S U & Nbhs U & isSubNbhs V S U}.

(*#[short(type="subTopologicalType")]
HB.structure Definition SubTopological (V : topologicalType) (S : pred V) :=
  { U of SubNbhs V S U & Topological U}.

#[short(type="subUniformType")]
HB.structure Definition SubUniform (V : uniformType) (S : pred V) :=
  { U of SubTopological V S U & Uniform U}.*)

#[short(type="subTopologicalType")]
HB.structure Definition SubTopological (V : topologicalType)
  (S : pred V) := {
  U of SubNbhs V S U & Topological U
  }.

Definition topU (V : Type) (S : pred V) (U : subChoiceType S) : Type
  := (initial_topology (\val : U -> V)).

Section SubType_isSubTopological.
Context (V : topologicalType) (S : pred V) (U : subChoiceType S).

Notation topU := (topU U).
HB.instance Definition _ := SubChoice.on topU.
HB.instance Definition _ := Nbhs.on topU.
HB.instance Definition _ := Topological.on topU.

#[local] Lemma top_continuous_valE : continuous (val : topU -> V).
Proof. exact: initial_continuous. Qed.

HB.instance Definition _ := @isSubNbhs.Build V S topU top_continuous_valE.

Check (topU : subNbhsType S).
Check (topU : subTopologicalType S).

End SubType_isSubTopological.

#[short(type="subConvexTvsType")]
HB.structure Definition SubConvexTvs (R : numDomainType)
  (V : convexTvsType R) (S : pred V) :=
  { U of SubTopological V S U & ConvexTvs R U & @GRing.SubLmodule R V S U
  }.

(* For lisibility, to be added to tvs.v *)
Lemma add_continuous (K : numDomainType) (E : convexTvsType K) : continuous (fun x : E * E => x.1 + x.2).
Proof. exact: add_continuous. Qed.

Section lmodule_isSubTvs.
Context (R : numFieldType) (V : convexTvsType R) (S : pred V) (U: subLmodType S).

Notation topU := (topU U).
Check topU : nbhsType.
HB.instance Definition _ := Nbhs.on topU.
Check topU : subChoiceType S.
HB.instance Definition _ := SubChoice.on topU.
Check topU : topologicalType.
HB.instance Definition _ := Topological.on topU.
Check topU : subNbhsType S.
HB.instance Definition _ := SubNbhs.on topU.
Check topU : uniformType.
HB.instance Definition _ := Uniform.on topU.
Check topU : lmodType R.
HB.instance Definition _ := GRing.Lmodule.on topU.
Check (topU : uniformType).
Check (topU : subLmodType S).

#[local] Lemma add_sub: continuous (fun x : topU * topU => x.1 + x.2).
Proof.
apply: continuous_comp_initial => -[/= x y].
pose h := fun xy : U * U => (\val xy.1, \val xy.2).
pose g := fun xy : V * V => xy.1 + xy.2.
rewrite (_ : _ \o _ = g \o h); last first.
  by apply/funext => i /=; rewrite GRing.valD.
apply: continuous_comp; last exact: add_continuous. 
apply: cvg_pair => //=.
- apply: (cvg_comp _ _ cvg_fst).
  exact: (continuous_valE (x : topU)).
- apply: (cvg_comp _ _ cvg_snd).
  exact: (continuous_valE (y : topU)).
Qed.

HB.instance Definition _ := @PreTopologicalNmodule_isTopologicalNmodule.Build topU add_sub.

Check (topU : TopologicalNmodule.type).

#[local] Lemma opp_sub : continuous (-%R : topU -> topU).
Proof.
apply: continuous_comp_initial => x.
rewrite (_ : _ \o _ = -%R \o \val); last first.
  by apply/funext=> i /=; rewrite GRing.valN.
apply: continuous_comp; first exact: continuous_valE.
exact: opp_continuous.
Qed.

HB.instance Definition _ := TopologicalNmodule_isTopologicalZmodule.Build topU opp_sub.

Check (topU : TopologicalZmodule.type).

#[local] Lemma scale_sub : continuous (fun z : R^o * topU => z.1 *: z.2).
Proof.
apply: continuous_comp_initial => - [] /= x /= y.
pose h := fun xy : R * U => (xy.1, \val xy.2).
pose g := fun xy : R * V => xy.1 *: xy.2.
rewrite (_ : _ \o _ = g \o h); last by apply/funext=> i /=; rewrite GRing.valZ.
apply: continuous_comp; last exact: scale_continuous.
  move => /= A [] /= [] a1 a2 [/=].
  move=> - [] /= r  /= - [] r0 /= br1.  
  move/(continuous_valE (y : topU)) =>  /= [na2 /= [] wo2 nay2 val2] A12.
  apply: filterS; first by exact: A12.
  exists ( ball_ [eta normr] x r ,na2) => //=; split; first by exists r.
  exists na2; split => //.
  - by apply: br1; move: H => /= [H _].  
  - by move: H => /= [_ H]; apply: val2.
Qed.

HB.instance Definition _ := TopologicalZmodule_isTopologicalLmodule.Build R topU scale_sub.

Check (topU : TopologicalLmodule.type R).

#[local] Lemma locally_convex_sub : exists2 B : set_system topU,
      (forall b, b \in B -> convex_set b) & basis B.
Proof.
move : (@locally_convex R V) => - [] B convexB [] openB /= genB.
exists  [set a | B(\val @` a)].
  move=> /= a; rewrite inE /=; rewrite -inE => H /= r s l ra sa.
  suff :  \val(r <|l|> s) \in \val @` a by rewrite !inE /= => -[] x ax /val_inj <-.
  have valr : \val r \in \val @` a by rewrite inE => /=; exists r; first by rewrite -inE.
  have vals : \val s \in \val @` a by rewrite inE => /=; exists s; first by rewrite -inE.
  move: (convexB (\val @` a) H (\val r) (\val s) l valr vals) => /=.
  by rewrite !GRing.valD !GRing.valZ //. 
split.
  move => A /= H. 
  have -> : A = \val @^-1`(\val @` A ).
    apply/seteqP; split => x /=; first by exists x.
    by move => -[y Ay] /val_inj <-. 
  apply:  open_comp; first by move => x _ ;apply: continuous_valE.
  by apply: openB.
(* the following should be simpler *)   
move=> /= x A nxA.
pose t:= nxA.
move: t => -[] /= /= b; rewrite /wopen => -[] /= [] c openc cA bx bA. 
have H: nbhs (val x) (val @` A). rewrite nbhsE /=.
exists (val @` b); last by move => z //= [] z0 bz valz; exists z0; first by apply: bA.
split => //=; last by exists x.
Print wopen.  admit. (*maybe ?*)
move: (genB (\val x) _ H).
rewrite /filter_from /=.
move => [] d [] Bd dx dC /=.
exists  (\val @^-1` d); last by move => y /= Cy; move: (dC (\val y) Cy) => /= [] t + /val_inj <-.  
split => //=. 
suff -> : [set \val (x : topU) | x in \val @^-1` d] = d by [].
rewrite eqEsubset; split => y; first by move=> [z + <-].
move=> dy /=. 
by move: (dC y dy) => /= [] t At valt; exists t; rewrite valt.

(*exists [set a | B(\val @` a)].
  move=> /= a; rewrite inE /=; rewrite -inE => H /= r s l ra sa.
  suff :  \val(r <|l|> s) \in \val @` a by rewrite !inE /= => -[] x ax /val_inj <-.
  have valr : \val r \in \val @` a by rewrite inE => /=; exists r; first by rewrite -inE.
  have vals : \val s \in \val @` a by rewrite inE => /=; exists s; first by rewrite -inE.
  move: (convexB (\val @` a) H (\val r) (\val s) l valr vals) => /=.
  by rewrite !GRing.valD !GRing.valZ //. 
split.
  move => A /= H. 
  have -> : A = \val @^-1`(\val @` A ).
    apply/seteqP; split => x /=; first by exists x.
    by move => -[y Ay] /val_inj <-. 
  apply:  open_comp; first by move => x _ ;apply: continuous_valE.
  by apply: openB.
(* the following should be simpler *)   
move=> /= x A [] A' []; rewrite /wopen => -[]/= C openC CA Ax AA'.
have H : nbhs (\val x) C by rewrite nbhsE /=; exists C =>//; split => //=; move: Ax; rewrite -CA /=. 
move: (genB (\val x) C H); rewrite /filter_from /=.
move => [] c [] Bc cx cC /=.
exists  (\val @^-1` c); last by move => y Cy; apply: AA'; rewrite -CA /=; apply:cC.
split => //=. 
suff -> : [set \val x | x in \val @^-1` c] = c by [].
move=> P T /=; rewrite eqEsubset; split => y; first by move=> [z + <-].
move=> cy /=.*)
(*nope*)
Admitted.
 
HB.instance Definition _ := @Uniform_isConvexTvs.Build R topU locally_convex_sub.

(*HB.instance Definition _ := @PreTopologicalLmod_isConvexTvs.Build R topU
                              add_sub scale_sub locally_convex_sub.*)
(* Does not work. why ?*)

Check (topU : convexTvsType R).

HB.instance Definition _ := ConvexTvs.on topU.
HB.instance Definition _ := GRing.SubLmodule.on topU.

Check (topU : convexTvsType R).
Check (topU : subLmodType S). 
Check (topU :  subConvexTvsType S).

End lmodule_isSubTvs. 
(*
HB.factory Record SubLmodule_isSubConvexTvs (R : realFieldType)
  (V : convexTvsType R) (S : pred V) U &  SubChoice V S U & @GRing.SubLmodule R V S U  := {
}.


HB.builders Context (R : realFieldType) (V : convexTvsType R) (S : pred V) U
            & SubLmodule_isSubConvexTvs R V S U. 

#[local] Definition topU : Type := (initial_topology (\val : U -> V)).

(*Because there is a new identificator, we need to redefine Topological.
When unifying, if it does not work immedialty, initial_topology will be unfolded *)
(*HB.instance Definition _ := Topological.on topU.*)
HB.instance Definition _ := SubChoice.on topU.
HB.instance Definition _ := Uniform.on topU.
HB.instance Definition _ := Topological.on topU.
HB.instance Definition _ := Nbhs.on topU.
HB.instance Definition _ := GRing.Lmodule.on topU.
Check (topU : SubChoice.type S).
Check (topU : pointedType). 
Check (topU : uniformType).
Check (topU : topologicalType). 
Check (topU : lmodType R).
Check (topU : preTopologicalLmodType R).
Check (topU : subLmodType S).

#[local] Lemma add_sub: continuous (fun x : topU * topU => x.1 + x.2).
Proof. Admitted.

HB.instance Definition _ := @PreTopologicalNmodule_isTopologicalNmodule.Build topU add_sub. 

Check (topU : TopologicalNmodule.type). 

#[local] Lemma opp_sub : continuous (-%R : topU -> topU). Admitted.

HB.instance Definition _ :=   TopologicalNmodule_isTopologicalZmodule.Build topU opp_sub.

Check (topU : TopologicalZmodule.type).

#[local] Lemma scale_sub : continuous (fun z : R^o * topU => z.1 *: z.2). Admitted.

HB.instance Definition _ := TopologicalZmodule_isTopologicalLmodule.Build R topU scale_sub.

Check (topU : TopologicalLmodule.type R).

#[local] Lemma add_unif_sub: unif_continuous (fun x : topU * topU => x.1 + x.2). Admitted.

HB.instance Definition _ := @PreUniformNmodule_isUniformNmodule.Build topU add_unif_sub. 

Check (topU : UniformNmodule.type). 

#[local] Lemma opp_unif_sub : unif_continuous (-%R : topU -> topU). Admitted.

HB.instance Definition _ :=   UniformNmodule_isUniformZmodule.Build topU opp_unif_sub.

Check (topU : UniformZmodule.type).

#[local] Lemma scale_unif_sub : unif_continuous (fun z : R^o * topU => z.1 *: z.2). Admitted.

HB.instance Definition _ := @UniformNmodule_isUniformLmodule.Build R topU scale_unif_sub.

Check (topU : UniformLmodule.type R).

#[local] Lemma locally_convex_sub : exists2 B : set_system topU,
      (forall b, b \in B -> convex_set b) & basis B. Admitted.
 
HB.instance Definition _ := @Uniform_isConvexTvs.Build R topU locally_convex_sub. 


(*Can't use that ? Maybe because we already have a uniform structure defined by initial_topology *)
(*HB.instance Definition _ := @PreTopologicalLmod_isConvexTvs.Build R topU
                              add_sub scale_sub locally_convex_sub.

 *)
(* Maybe this is enough instead of all the Top/Unif N/Z/Mlomd *)

#[local] Lemma continuous_valE : continuous (val : topU -> V).
Proof. exact: initial_continuous. Qed.

HB.instance Definition _ := isSubConvexTvs.Build R V S topU continuous_valE.

Check (topU : SubType.type S).
Check (topU : @GRing.SubLmodule.type R V S).
Check (topU : NbhsZmodule.type). 
Check (topU : ConvexTvs.type R).
Check (topU : SubChoice.type S).
Check (topU : PreUniformLmodule.type R).
Check (topU : UniformLmodule.type R).
Check (topU : topologicalZmodType). 
Check (topU : uniformType).
HB.about subConvexTvsType.
Fail Check (topU : subConvexTvsType S).


Fail HB.end.
*)



(* TODO: moved to normed_module.v *)
#[short(type="subNormedModType")]
HB.structure Definition SubNormedModule (R : numDomainType)
  (V : normedModType R) (S : pred V) :=
  { U of SubChoice V S U & NormedModule R U & @GRing.SubLmodule R V S U
       & @SubNormedZmodule(*Zmodule_isSubSemiNormed*) R V S U & @SubConvexTvs R V S U}. 



Lemma myfilter {R : realFieldType} (U : normedZmodType R) x : Filter
    [set P | (exists2 i : set (pseudoMetric_normed U * pseudoMetric_normed U),
                pseudoMetric_from_normedZmodType.ent i & xsection i x `<=` P)].
Proof.
apply: Build_Filter => /=.
- exists setT.
    have := @entourageT (pseudoMetric_normed U).
    exact.
  by [].
- move=> A B/= [A' entA' A'A] [B' entB' B'B].
  exists (A' `&` B') => //.
  Import pseudoMetric_from_normedZmodType.
  rewrite entourageE.
  rewrite /entourage_.
  case: entA' => r/= r0 HA'.
  case: entB' => d/= d0 HB'.
  exists (Num.min r d) => /=.
    by rewrite lt_min r0.
    move=> z/= Hz.
  split.
    apply: HA' => /=.
    do 3 red.
    rewrite (lt_le_trans Hz)//.
    by rewrite ge_min lexx.
  apply: HB' => /=.
  do 3 red.
  rewrite (lt_le_trans Hz)//.
  by rewrite ge_min lexx orbT.
  by rewrite xsectionI; apply: setISS.
- move=> P Q PQ [A entA AP].
  exists A => //.
  exact: (subset_trans AP).
Qed.



HB.factory Record SubLmodule_isSubNormedmodule (R : realFieldType)
  (V : normedModType R) (S : pred V) U &  SubChoice V S U & @GRing.SubLmodule R V S U  := {
}.

HB.builders Context R V S U & SubLmodule_isSubNormedmodule R V S U.

Local Definition normu := fun (u : U)=> `|\val u|.

#[local] Lemma ler_normuD (x y :U): normu (x + y) <= normu x + normu y.
Proof.
by rewrite /normu GRing.valD; exact: ler_normD.
Qed.

#[local] Lemma normru0_eq0 x: normu x = 0 -> x = 0.
Proof.
move/eqP; rewrite normr_eq0 /normu -(@GRing.val0 V S U) =>/eqP. 
by exact: val_inj.
Qed.

#[local] Lemma normruMn x n: normu (x *+ n) = normu x *+ n.
Proof.
by rewrite /normu raddfMn /=; exact: normrMn.
Qed. 

#[local] Lemma normruN x: normu (- x) = normu x.
Proof.
by rewrite /normu raddfN /=; exact: normrN.
Qed.

#[local] Lemma normruZ (l : R) (x : U): normu (l *: x) = `|l| * normu x.
Proof.
by rewrite /normu GRing.valZ; exact: normrZ.
Qed.

HB.instance Definition _ :=
  @Lmodule_isNormed.Build R U normu ler_normuD normruZ normru0_eq0.

HB.instance Definition _ := NormedZmod_PseudoMetric_eq.Build R U erefl.

HB.instance Definition _ :=
  @Lmodule_isNormed.Build R U normu ler_normuD normruZ normru0_eq0.
(* NB : when defining intermediate instances first, via @Num.Zmodule_isNormed.Build, this command check
but then we have Fail Check (U : pseudometricnormedzmodtype R) and Fail Check (U
: normedModtype R).
 *)
Check (U : normedModType R).

#[local] Lemma normu_valE : forall x, @Num.norm _ V ((val : U -> V) x) = @Num.norm _ U x.
Proof. by []. Qed.

HB.instance Definition _ :=  Zmodule_isSubNormed.Build _ _ _ U normu_valE.
(* TODO : why is the U necessary ?*)

Check (U : subNormedZmodType S).

#[local] Lemma continuous_valE : continuous (val : U -> V).
Proof.
move=> /= x.
red.
set rhs := (X in _ --> X).
apply/cvgrPdist_le => //=.
  by apply: myfilter.
move=> e e0.
near=> t.
rewrite -GRing.valN.
rewrite -GRing.valD.
rewrite norm_valE.
near: t.
move: e e0.
by apply/cvgrPdist_le.
Unshelve. all: by end_near. Qed.

HB.instance Definition _ :=  isSubNbhs.Build _ _ U continuous_valE.

Check (U : subConvexTvsType S).

Check (U : subNormedModType S). 

HB.instance Definition _ := SubLmodule_isSubNormedmodule.Build _ _ _ U.
HB.end.

(* TODO : use a lightweight factory to make every subLmodType a subnormedmodtype *)

Module Lingraph.
Section Lingraphsec.
Variables (R : numDomainType) (V : lmodType R).

Definition graph := V -> R -> Prop.

Definition linear_graph (f : graph) :=
  forall v1 v2 l r1 r2, f v1 r1 -> f v2 r2 -> f (v1 + l *: v2) (r1 + l * r2).

Variable f : graph.
Hypothesis lrf : linear_graph f.

Lemma lingraph_00 x r : f x r -> f 0 0.
Proof.
suff -> : f 0 0 = f (x + (-1) *: x) (r + (-1) * r) by move=> h; apply: lrf.
by rewrite scaleNr mulNr mul1r scale1r !subrr.
Qed.

Lemma lingraph_scale x r l : f x r -> f (l *: x) (l * r).
Proof.
move=> fxr.
have -> : f (l *: x) (l * r) = f (0 + l *: x) (0 + l * r) by rewrite !add0r.
by apply: lrf=> //; exact: lingraph_00 fxr.
Qed.

Lemma lingraph_add x1 x2 r1 r2 : f x1 r1 -> f x2 r2 -> f (x1 - x2) (r1 - r2).
Proof.
have -> : x1 - x2 = x1 + (-1) *: x2 by rewrite scaleNr scale1r.
have -> : r1 - r2 = r1 + (-1) * r2 by rewrite mulNr mul1r.
exact: lrf.
Qed.

Definition add_line f w a := fun v r => exists (v' : V) (r' : R) (lambda : R),
  [/\ f v' r', v = v' + lambda *: w & r = r' + lambda * a].

End Lingraphsec.
End Lingraph.

Module HBPreparation.
Section HBPreparation.
Import Lingraph.
Variables (R : realType) (V : lmodType R) (F : pred V).
Variables (F' : subLmodType F) (phi : {linear F' -> R}) (p : V -> R).

Implicit Types (f g : graph V).

Hypothesis phi_le_p : forall v, (phi v) <= (p (val v)).

Hypothesis p_cvx : (@convex_function  R V [set: V]  p).

Definition extend_graph f := forall (v : F'), f (\val v) (phi v).

Definition le_graph p f :=  forall v r, f v r -> r <= p v.

Definition functional_graph f := forall v r1 r2, f v r1 -> f v r2 -> r1 = r2.

Definition linear_graph f :=
   forall v1 v2 l r1 r2,  f v1 r1 -> f v2 r2 -> f (v1 + l *: v2) (r1 + l * r2).

Definition le_extend_graph f :=
  [/\ functional_graph f, linear_graph f, le_graph p f &  extend_graph f].

Record zorn_type : Type := ZornType
  {carrier : graph V; specP : le_extend_graph carrier}.

Let spec_phi : le_extend_graph (fun v r => exists2 y : F', v = val y & r = phi y).
Proof.
split.
- by move=> v r1 r2 [y1 ->  ->] [y2 + ->] => /val_inj ->.
- move => v1 v2 l r1 r2 [y1 -> ->] [y2 ->  ->].
  by exists (y1 + l *: y2); rewrite !linearD !linearZ.
- by move=> r v [y -> ->].
- by move=> v; exists v.
Qed.

Definition zphi := ZornType spec_phi.

Lemma zorn_type_eq z1 z2 : carrier z1 = carrier z2 -> z1 = z2.
Proof.
case: z1 => m1 pm1; case: z2 => m2 pm2 /= e; rewrite e in pm1 pm2 *.
by congr ZornType; exact: Prop_irrelevance.
Qed.

Definition zornS (z1 z2 : zorn_type):=
  forall x y, (carrier z1 x y) ->  (carrier z2 x y ).

(* Zorn applied to the relation of extending the graph of the first function: *)
Lemma zornS_ex : exists g : zorn_type, forall z, zornS g z -> z = g.
Proof.
pose Rbool x y := `[< zornS x y >].
have RboolP z t : Rbool z t <-> zornS z t by split => /asboolP.
suff [t st] : exists t : zorn_type, forall s : zorn_type, Rbool t s -> s = t.
  by exists t; move => z /RboolP tz; exact: st.
apply: (@Zorn zorn_type Rbool); first by move=> t; exact/RboolP.
- by move=> r s t /RboolP a /RboolP b; apply/RboolP => x y /a /b.
- move=> r s /RboolP a /RboolP b; apply: zorn_type_eq.
  by apply: funext => z; apply: funext => h; apply: propext; split => [/a | /b].
- move => A Amax.
  have [[w Aw] | eA] := lem (exists a, A a); last first.
    by exists zphi => a Aa; elim: eA; exists a.
  (* g is the union of the graphs indexed by elements in a *)
  pose g v r := exists2 a, A a & (carrier a v r).
  have g_fun : functional_graph g.
    move=> v r1 r2 [a Aa avr1] [b Ab bvr2].
    have [] : Rbool a b \/ Rbool b a by exact: Amax.
      rewrite /Rbool /RboolP /zornS; case: b Ab bvr2 {Aa}.
      move => s2 [fs2 _ _ _] /= _ s2vr2 /asboolP ecas2.
     by move/ecas2: avr1 => /fs2 /(_ s2vr2).
   rewrite /Rbool /RboolP /zornS.
   case: a Aa avr1 {Ab} => s1 [fs1 _ _ _] /= _ s1vr1 /asboolP ecbs1.
   by move/ecbs1: bvr2; apply: fs1.
have g_lin : linear_graph g.
  move=> v1 v2 l r1 r2 [a1 Aa1 c1] [a2 Aa2 c2].
  have [/RboolP sc12 | /RboolP sc21] := Amax _ _ Aa1 Aa2.
  - have {c1 sc12 Aa1 a1} c1 :  carrier a2 v1 r1 by apply: sc12.
    by exists a2 => //; case: a2 {Aa2} c2 c1 => c /= [_ hl _ _] *; exact: hl.
  - have {c2 sc21 Aa2 a2} c2 :  carrier a1 v2 r2 by apply: sc21.
    by exists a1 => //; case: a1 {Aa1} c2 c1 => c /= [_ hl _ _] *; exact: hl.
have g_majp : le_graph p g.
  by move=> v r [[c/= [fs1 ls1 ms1 ps1]]]/= _ => /ms1.
have g_prol : extend_graph g.
   by move=> *; exists w=> //; case: w Aw => [c [_ _ _ hp]] _ //=; exact: hp.
have spec_g : le_extend_graph g by split.
pose zg := ZornType spec_g.
by exists zg => [a Aa]; apply/RboolP; rewrite /zornS => v r cvr; exists a.
Qed.

Variable g : zorn_type.

Hypothesis gP : forall z, zornS g z -> z = g.

(*The next lemma proves that when z is of zorn_type, it can be extended on any
real line directed by an arbitrary vector v *)

Lemma domain_extend  (z : zorn_type) v :
 exists2 ze : zorn_type, zornS z ze & exists r, (carrier ze) v r.
Proof.
case: (lem (exists r, (carrier z v r))).
  by case=> r rP; exists z => //; exists r.
case: z => [c [fs1 ls1 ms1 ps1]] /= nzv.
have c00 : c 0 0.
  have <- : phi 0 = 0 by rewrite linear0.
  by move: ps1; rewrite /extend_graph /= => /(_ 0) /=; rewrite GRing.val0; apply.
have [a aP] : exists a, forall (x : V) (r lambda : R), c x r ->
    r + lambda * a <= p (x + lambda *: v).
  suff [a aP] : exists a, forall (x : V) (r lambda : R), c x r -> 0 < lambda ->
    r + lambda * a <= p (x + lambda *: v) /\ r - lambda * a <= p (x - lambda *: v).
     exists a=> x r lambda cxr.
     have {aP} aP := aP _ _ _ cxr.
     case: (ltrgt0P lambda) ; [by case/aP | move=> ltl0 | move->]; last first.
       by rewrite mul0r scale0r !addr0; apply: ms1.
     rewrite -[lambda]opprK scaleNr mulNr.
     have /aP [] : 0 < - lambda by rewrite oppr_gt0.
     done.
   pose b (x : V) r lambda : R := (p (x + lambda *: v) - r) / lambda.
   pose a (x : V) r lambda : R := (r - p (x - lambda *: v)) / lambda.
   have le_a_b x1 x2 r1 r2 s t : c x1 r1 -> c x2 r2 -> 0 < s -> 0 < t -> a x1 r1 s <= b x2 r2 t.
     move=> cxr1 cxr2 lt0s lt0t; rewrite /a /b.
     rewrite ler_pdivlMr // mulrAC ler_pdivrMr // mulrC [_ * s]mulrC.
     rewrite !mulrDr !mulrN lerBlDr addrAC lerBrDr.
     have /ler_pM2r <- : 0 < (s + t) ^-1 by rewrite invr_gt0 addr_gt0.
     set y1 : V := _ + _ *: _; set y2 : V :=  _ - _ *: _.
     set rhs := (X in _ <= X).
     have step1 : p (s  / (s + t) *: y1 + t  / (s + t) *: y2) <= rhs.
       rewrite /rhs !mulrDl ![_  * _ / _]mulrAC.
       pose st := Itv01 (divDl_ge0 (ltW lt0s) (ltW lt0t)) ((divDl_le1 (ltW lt0s) (ltW lt0t))).
       move: (p_cvx st (in_setT y1) (in_setT y2)).
       by rewrite /conv /= [X in ((_ <= X)-> _)]/conv /= divD_onem /=.
     apply: le_trans step1 => {rhs}.
     set u : V := (X in p X).
     have {u y1 y2} -> : u = t  / (s + t) *: x1 + s / (s + t) *: x2.
       rewrite /u ![_ / _]mulrC -!scalerA -!scalerDr /y1 /y2; congr (_ *: _).
       by rewrite !scalerDr addrCA scalerN scalerA [s * t]mulrC -scalerA addrK.
     set l := t / _; set m := s / _; set lhs := (X in X <= _).
     have {lhs} -> : lhs = l * r1 + m * r2.
       by rewrite /lhs mulrDl ![_  * _ / _]mulrAC.
     apply: ms1; apply: (ls1) => //.
     rewrite -[_ *: _]add0r -[_ * _] add0r; apply: ls1 => //.
     pose Pa : set R := fun r =>  exists x1, exists r1, exists s1,
       [/\ c x1 r1, 0 < s1 & r = a x1 r1 s1].
     pose Pb : set R := fun r =>  exists x1, exists r1, exists s1,
       [/\ c x1 r1, 0 < s1 & r = b x1 r1 s1].
     pose sa := reals.sup Pa. (* This is why we need realTypes, we need p with values in a realType *)
     have Pax : Pa !=set0 by exists (a 0 0 1); exists 0; exists 0; exists 1; split.
     have ubdP : ubound Pa sa.
       apply: sup_upper_bound; split => //=.
       exists (b 0 0 1) =>/= x [y [r [s [cry lt0s ->]]]]; apply: le_a_b => //; exact: ltr01.
     have saP: forall u : R, ubound Pa u -> sa <= u by move=> u; apply: ge_sup.
     pose ib := reals.inf Pb. (* This is why we need realTypes, we need P with values in a realType *)
     have Pbx : Pb !=set0 by exists (b 0 0 1); exists 0; exists 0; exists 1; split.
     have ibdP : lbound Pb ib.
       by apply: ge_inf; exists (a 0 0 1) =>/= x [y [r [s [cry lt0s ->]]]]; apply: le_a_b => //; exact: ltr01.
     have ibP: forall u : R, lbound Pb u -> u <= ib by move=> u; apply: lb_le_inf Pbx.
     have le_sa_ib : sa <= ib.
       apply: saP=> r' [y [r [l [cry lt0l -> {r'}]]]].
       apply: ibP=> s' [z [s [m [crz lt0m -> {s'}]]]]; exact: le_a_b.
     pose alpha := ((sa + ib) / 2%:R).
     have le_alpha_ib : alpha <= ib by rewrite /alpha midf_le.
     have le_sa_alpha : sa <= alpha by rewrite /alpha midf_le.
     exists alpha => x r l cxr lt0l; split.
     - suff : alpha <= b x r l.
         by rewrite /b; move/ler_pdivlMr: lt0l->; rewrite lerBrDl mulrC.
       by apply: le_trans le_alpha_ib _; apply: ibdP; exists x; exists r; exists l.
     - suff : a x r l <= alpha.
         by rewrite /a; move/ler_pdivrMr: lt0l-> ; rewrite lerBlDl -lerBlDr mulrC.
       by apply: le_trans le_sa_alpha; apply: ubdP; exists x; exists r; exists l.
pose z' := fun k r =>  exists v' : V, exists r' : R, exists lambda : R,
                        [/\ c v' r', k = v' + lambda *: v & r = r' + lambda * a].
have z'_extends :  forall v r, c v r -> z' v r.
  by move=> x r cxr; exists x; exists r; exists 0; split; rewrite // ?scale0r ?mul0r !addr0.
have z'_prol : extend_graph z'.
  by move=> x; exists (val x); exists (phi x); exists 0; split; rewrite // ?scale0r ?mul0r !addr0.
have z'_maj_by_p : le_graph p z' by move=> x r [w [s [l [cws -> ->]]]]; apply: aP.
have z'_lin : linear_graph z'.
   move=> x1 x2 l r1 r2 [w1 [s1 [m1 [cws1 -> ->]]]] [w2 [s2 [m2 [cws2 -> ->]]]].
   set w := (X in z' X _); set s := (X in z' _ X).
   have {w} -> : w = w1 + l *: w2 + (m1 + l * m2) *: v.
     by rewrite /w !scalerDr !scalerDl scalerA -!addrA [X in _ + X]addrCA.
   have {s} -> : s = s1 + l * s2 + (m1 + l * m2) * a.
     by rewrite /s !mulrDr !mulrDl mulrA -!addrA [X in _ + X]addrCA.
   exists (w1 + l *: w2); exists (s1 + l * s2); exists (m1 + l * m2); split=> //.
   by exact: ls1.
have z'_functional : functional_graph z'.
  move=> w r1 r2 [w1 [s1 [m1 [cws1 -> ->]]]] [w2 [s2 [m2 [cws2 e1 ->]]]].
  have h1 (x : V) (r l : R) : x = l *: v ->  c x r -> x = 0 /\ l = 0.
    move=> -> cxr; case: (l =P 0) => [-> | /eqP ln0]; first by rewrite scale0r.
     suff cvs: c v (l^-1 * r) by elim:nzv; exists (l^-1 * r).
     suff -> : v = l ^-1 *: (l *: v).
       have -> : c(l^-1*:(l*:v))(l^-1*r) = c(0 + l^-1*:(l*:v))(0+l^-1*r) by rewrite !add0r.
       by apply: ls1=> //; apply: linrel_00 fxr.
     by rewrite scalerA mulVf ?scale1r.
   have [rw12 erw12] : exists r,  c (w1 - w2) r.
     exists (s1+(-1)*s2).
     have -> : w1 - w2 = w1 + (-1) *: w2 by rewrite scaleNr scale1r.
     by apply: ls1.
   have [ew12 /eqP]: w1 - w2 = 0 /\ (m2 - m1 = 0).
     apply: h1 erw12; rewrite scalerBl; apply/eqP; rewrite subr_eq addrC addrA.
     by rewrite -subr_eq opprK e1.
   suff -> : s1 = s2 by rewrite subr_eq0=> /eqP->.
   by apply: fs1 cws2; move/eqP: ew12; rewrite subr_eq0=> /eqP<-.
have z'_spec : le_extend_graph z' by split.
pose zz' := ZornType z'_spec.
exists zz'; rewrite /zornS => //=; exists a; exists 0; exists 0; exists 1.
by rewrite add0r mul1r scale1r add0r; split.
Qed.

Let tot_g v : exists r, carrier g v r.
Proof.
have [z /gP sgz [r zr]]:= domain_extend g v.
by exists r; rewrite -sgz.
Qed.

Lemma hb_witness : exists h : V -> R, forall v r, carrier g v r <-> (h v = r).
Proof.
move: (choice tot_g) => [h hP]; exists h => v r; split; last by move<-.
case: g gP tot_g hP => c /= [fg lg mg pg] => gP' tot_g' hP cvr.
by have -> // := fg v r (h v).
Qed.

End HBPreparation.
End HBPreparation.

(* NB: could go to convex.v *)
Section hahn_banach.
Import Lingraph.
Import HBPreparation.
(* Now we prove HahnBanach on functions*)
(* We consider R a real (=ordered) field with supremum, and V a (left) module
   on R. We do not make use of the 'vector' interface as the latter enforces
   finite dimension. *)
Variables (R : realType) (V : lmodType R) (F : pred V).

Variables (F' : subLmodType F) (f : {linear F' -> R}) (p : V -> R).

Hypothesis p_cvx : @convex_function R V [set: V] p.

Hypothesis f_bounded_by_p : forall (z : F'), (f z  <= p (\val z)).

Theorem hahn_banach_extension : exists g : {scalar V},
  (forall x, g x <= p x) /\ (forall z : F', g (\val z) = f z).
Proof.
pose graphF (v : V) r := exists2 z : F', v = \val z & r = f z.
have [z zmax]:= zornS_ex f_bounded_by_p.
have [g gP]:= (hb_witness p_cvx zmax).
have scalg : linear_for *%R g.
  case: z {zmax} gP=> [c [_ ls1 _ _]] /= gP.
  have addg : additive g.
    by move=> w1 w2;  apply/gP; apply: lingraph_add =>//; apply/gP.
  suff scalg : scalable_for  *%R g.
    by move=> a u v; rewrite -gP (addrC _ v) (addrC _ (g v)); apply: ls1; apply /gP.
  by move=> w l; apply/gP; apply: lingraph_scale=> //; apply/gP.
pose H := GRing.isLinear.Build _ _ _ _ g scalg.
pose g' : {linear V -> R | *%R} := HB.pack g H.
exists g'.
split; last first.
  by move => z'; apply/gP; case: z {zmax gP} => [c [_ _ _ pf]] /=; exact: pf.
by case: z {zmax} gP => [c [_ _ bp _]] /= gP => x; apply: bp; apply/gP.
Qed.

End hahn_banach.

(* TODO : to define on tvs, characterize the topology of a tvs via its pseudonorms,
and the continuity of linear continuous functions via the pseudonorms. *)

Section hahn_banach_normed.
Variable (R : realType) (V : normedModType R) (F : pred V)
  (F' : subNormedModType F) (f : {linear_continuous F' -> R}).


(*To use the thm on a F': subLmodType F, use @SubLmodule_isSubNormedmodule.Build.
TODO : a lightweight factory  *)
Theorem hahn_banach_extension_normed :
  exists g : {linear_continuous V -> R}, (forall x, (g (val x) = f x)).
Proof.
have [r [ltr0 fxrx]] : exists2 r, r > 0 & forall (z : F'), `|f z| <= `|val z| * r.
  suff: \forall r \near +oo, forall x : F', `|f x| <= r * `|x|.
    move=> [t [_ tf]].
    exists (`|t| + 1); first by rewrite ltr_wpDl.
    by move=> z; rewrite mulrC norm_valE tf// (le_lt_trans (ler_norm _))// ltrDl.
  exact/linear_boundedP/continuous_linear_bounded/cts_fun.
pose p := fun x : V => `|x| * r.
have convp : @convex_function _ _ [set: V] p.
  rewrite /convex_function /conv => l v1 v2 _ _ /=.
  rewrite [X in (_ <= X)]/conv /= /p.
  apply: le_trans.
    have H : `|l%:num *: v1 + (l%:num).~ *: v2| <= `|l%:num *: v1|  + `|l%:num.~ *: v2|.
      exact: ler_normD.
    by apply: (@ler_pM _ _ _ r r _ _ H) => //; apply: ltW.
   rewrite mulrDl !normrZ -![_ *: _]/(_ * _).
   have -> : `|l%:num| = l%:num by apply/normr_idP.
   have -> : `|l%:num.~| = l%:num.~ by apply/normr_idP; apply: onem_ge0.
   by rewrite !mulrA.
have majfp : forall z : F', f z <= p (\val z).
  move => z; rewrite /(p _) ; apply : le_trans; last by [].
  exact: ler_norm.
have [g [majgp F_eqgf {majfp}]] := hahn_banach_extension convp majfp.
have ling : linear (g : V -> R) by exact: linearP.
have contg : (continuous (g : V -> R)).
  move=> x; rewrite /cvgP; apply: continuousfor0_continuous.
  apply: bounded_linear_continuous.
  exists r; split; first exact: gtr0_real.
  move => M m1; rewrite nbhs_ballP;  exists 1 => /=; first by [].
  move => y; rewrite -ball_normE //= sub0r => y1.
  rewrite ler_norml; apply/andP; split.
  - rewrite lerNl  -linearN; apply: (le_trans (majgp (- y))).
    by rewrite /p -[X in _ <= X]mul1r; apply: ler_pM; rewrite ?normr_ge0 ?ltW.
  - apply: (le_trans (majgp y)); rewrite /p -[X in _ <= X]mul1r -normrN.
    by apply: ler_pM; rewrite ?normr_ge0 ?ltW.
pose Hg := isLinearContinuous.Build _ _ _ _ g ling contg.
pose g': {linear_continuous V -> R | *%R} := HB.pack (g : V -> R) Hg.
by exists g'.
Qed.

End hahn_banach_normed.
