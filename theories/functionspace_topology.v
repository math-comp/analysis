(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice div.
From mathcomp Require Import seq fintype bigop order ssralg ssrnum finmap matrix.
Require Import boolp reals classical_sets posnum topology.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Local Notation "B \o A" :=
  ([set xy | exists2 z, A (xy.1, z) & B (z, xy.2)]) : classical_set_scope.

Local Notation "A ^-1" := ([set xy | A (xy.2, xy.1)]) : classical_set_scope.

Local Notation "'to_set' A x" := ([set y | A (x, y)])
  (at level 0, A at level 0) : classical_set_scope.
Class UltraFilter {T} (F : set (set T)) := {
  ultra_proper :> ProperFilter F ;
  max_filter : forall G : set (set T), ProperFilter G -> F `<=` G -> G = F
}.

Section Tychonoff.

Lemma ultra_cvg_clusterE (T : topologicalType) (F : set (set T)) :
  UltraFilter F -> cluster F = [set p | F --> p].
Proof.
move=> FU; rewrite predeqE => p; split.
  by rewrite cluster_cvgE => - [G GF [cvGp /max_filter <-]].
by move=> cvFp; rewrite cluster_cvgE; exists F; [apply: ultra_proper|split].
Qed.

Lemma ultraFilterLemma T (F : set (set T)) :
  ProperFilter F -> exists G, UltraFilter G /\ F `<=` G.
Proof.
move=> FF.
set filter_preordset := ({G : set (set T) & ProperFilter G /\ F `<=` G}).
set preorder := fun G1 G2 : filter_preordset => projT1 G1 `<=` projT1 G2.
suff [G Gmax] : exists G : filter_preordset, premaximal preorder G.
  have [GF sFG] := projT2 G; exists (projT1 G); split=> //; split=> // H HF sGH.
  have sFH : F `<=` H by apply: subset_trans sGH.
  have sHG : preorder (existT _ H (conj HF sFH)) G by apply: Gmax.
  by rewrite predeqE => ?; split=> [/sHG|/sGH].
have sFF : F `<=` F by [].
apply: (ZL_preorder ((existT _ F (conj FF sFF)) : filter_preordset)) =>
  [?|G H I sGH sHI ? /sGH /sHI|A Atot] //.
case: (pselect (A !=set0)) => [[G AG] | A0]; last first.
  exists (existT _ F (conj FF sFF)) => G AG.
  by have /asboolP := A0; rewrite asbool_neg => /forallp_asboolPn /(_ G).
have [GF sFG] := projT2 G.
suff UAF : ProperFilter (\bigcup_(H in A) projT1 H).
  have sFUA : F `<=` \bigcup_(H in A) projT1 H.
    by move=> B FB; exists G => //; apply: sFG.
  exists (existT _ (\bigcup_(H in A) projT1 H) (conj UAF sFUA)) => H AH B HB /=.
  by exists H.
apply Build_ProperFilter.
  by move=> B [H AH HB]; have [HF _] := projT2 H; apply: (@filter_ex _ _ HF).
split; first by exists G => //; apply: filterT.
  move=> B C [HB AHB HBB] [HC AHC HCC]; have [sHBC|sHCB] := Atot _ _ AHB AHC.
    exists HC => //; have [HCF _] := projT2 HC; apply: filterI HCC.
    exact: sHBC.
  exists HB => //; have [HBF _] := projT2 HB; apply: filterI HBB _.
  exact: sHCB.
move=> B C SBC [H AH HB]; exists H => //; have [HF _] := projT2 H.
exact: filterS HB.
Qed.

Lemma compact_ultra (T : topologicalType) :
  compact = [set A | forall F : set (set T),
  UltraFilter F -> F A -> A `&` [set p | F --> p] !=set0].
Proof.
rewrite predeqE => A; split=> Aco F FF FA.
  by have /Aco [p [?]] := FA; rewrite ultra_cvg_clusterE; exists p.
have [G [GU sFG]] := ultraFilterLemma FF.
have /Aco [p [Ap]] : G A by apply: sFG.
rewrite /= -[_ --> p]/([set _ | _] p) -ultra_cvg_clusterE.
by move=> /(cvg_cluster sFG); exists p.
Qed.

Lemma in_ultra_setVsetC T (F : set (set T)) (A : set T) :
  UltraFilter F -> F A \/ F (~` A).
Proof.
move=> FU; case: (pselect (F (~` A))) => [|nFnA]; first by right.
left; suff : ProperFilter (filter_from (F `|` [set A `&` B | B in F]) id).
  move=> /max_filter <-; last by move=> B FB; exists B => //; left.
  by exists A => //; right; exists setT; [apply: filterT|rewrite setIT].
apply filter_from_proper; last first.
  move=> B [|[C FC <-]]; first exact: filter_ex.
  apply: contrapT => /asboolP; rewrite asbool_neg => /forallp_asboolPn AC0.
  by apply: nFnA; apply: filterS FC => p Cp Ap; apply: (AC0 p).
apply: filter_from_filter.
  by exists A; right; exists setT; [apply: filterT|rewrite setIT].
move=> B C [FB|[DB FDB <-]].
  move=> [FC|[DC FDC <-]]; first by exists (B `&` C)=> //; left; apply: filterI.
  exists (A `&` (B `&` DC)); last by rewrite setICA.
  by right; exists (B `&` DC) => //; apply: filterI.
move=> [FC|[DC FDC <-]].
  exists (A `&` (DB `&` C)); last by rewrite setIA.
  by right; exists (DB `&` C) => //; apply: filterI.
exists (A `&` (DB `&` DC)); last by move=> ??; rewrite setIACA setIid.
by right; exists (DB `&` DC) => //; apply: filterI.
Qed.

Lemma ultra_image (T U : Type) (f : T -> U) (F : set (set T)) :
  UltraFilter F -> f @` setT = setT -> UltraFilter [set f @` A | A in F].
Proof.
move=> FU fsurj; split; first exact: proper_image.
move=> G GF sfFG; rewrite predeqE => A; split; last exact: sfFG.
move=> GA; exists (f @^-1` A); last by rewrite image_preimage.
have [//|FnAf] := in_ultra_setVsetC (f @^-1` A) FU.
have : G (f @` (~` (f @^-1` A))) by apply: sfFG; exists (~` (f @^-1` A)).
suff : ~ G (f @` (~` (f @^-1` A))) by [].
rewrite preimage_setC image_preimage // => GnA.
by have /filter_ex [? []] : G (A `&` (~` A)) by apply: filterI.
Qed.

Lemma tychonoff (I : eqType) (T : I -> topologicalType)
  (A : forall i, set (T i)) :
  (forall i, compact (A i)) ->
  @compact (product_topologicalType T)
    [set f : forall i, T i | forall i, A i (f i)].
Proof.
move=> Aco; rewrite compact_ultra => F FU FA.
set subst_coord := fun (i : I) (pi : T i) (f : forall x : I, T x) (j : I) =>
  if eqP is ReflectT e then ecast i (T i) (esym e) pi else f j.
have subst_coordT i pi f : subst_coord i pi f i = pi.
  rewrite /subst_coord; case eqP => // e.
  by rewrite (eq_irrelevance e (erefl _)).
have subst_coordN i pi f j : i != j -> subst_coord i pi f j = f j.
  move=> inej; rewrite /subst_coord; case: eqP => // e.
  by move: inej; rewrite {1}e => /negP.
have pr_surj i : @^~ i @` (@setT (forall i, T i)) = setT.
  rewrite predeqE => pi; split=> // _.
  by exists (subst_coord i pi (fun _ => point))=> //; rewrite subst_coordT.
set pF := fun i => [set @^~ i @` B | B in F].
have pFultra : forall i, UltraFilter (pF i).
  by move=> i; apply: ultra_image (pr_surj i).
have pFA : forall i, pF i (A i).
  move=> i; exists [set g | forall i, A i (g i)] => //.
  rewrite predeqE => pi; split; first by move=> [g Ag <-]; apply: Ag.
  move=> Aipi; have [f Af] := filter_ex FA.
  exists (subst_coord i pi f); last exact: subst_coordT.
  move=> j; case: (eqVneq i j); first by case: _ /; rewrite subst_coordT.
  by move=> /subst_coordN ->; apply: Af.
have cvpFA i : A i `&` [set p | pF i --> p] !=set0.
  by rewrite -ultra_cvg_clusterE; apply: Aco.
exists (fun i => get (A i `&` [set p | pF i --> p])).
split=> [i|]; first by have /getPex [] := cvpFA i.
by apply/cvg_sup => i; apply/cvg_image=> //; have /getPex [] := cvpFA i.
Qed.

End Tychonoff.

Definition equicontinuous {X : topologicalType} {V : uniformType}
  (W : set (X -> V)) :=
  forall x (E: set (V * V)), entourage E -> exists (U : set (X)), 
    nbhs x U /\ (forall f y, W f -> U y -> E(f x, f y)).

Definition uniformlyEquicontinuous {X V : uniformType} (W : set (X -> V)):=
  forall (E: set (V * V)), entourage E -> exists (D : set (X*X)), 
    entourage D /\ forall f x y, W f -> D(x,y) -> E(f x, f y).

Section Evaluators.
Context {X : choiceType}.
Context {K : forall x:X, topologicalType}.
Definition evaluator_dep (x : X) (f : product_topologicalType K) := f x.

Lemma evaluator_depE x f : evaluator_dep x f = f x.
Proof. by []. Qed.

Definition xval {x : X} (y : K x) i : K i := 
  match (pselect `[< x = i >]) return K i with 
  | left r => ltac:(move/asboolP:r => <-; exact y)
  | right _ => point
  end.

Lemma evaluator_dep_continuous x: continuous (evaluator_dep x).
Proof.
move=> f.
have /cvg_sup/(_ x)/cvg_image : (f --> f) by apply: cvg_id.
set P := ( x in (x -> _) -> _).
have P' : P. {
  rewrite /P eqEsubset; split => y /=.
  - by [].
  - move=> _; exists (xval y) => //.
    rewrite /xval; case (pselect _).
    + move/asboolP => Q; rewrite -Eqdep_dec.eq_rect_eq_dec => //.
      move=> p q ; generalize (p = q);  exact: pselect.
    + by move => Q; contradict Q; apply/ asboolP.
} 
move/(_ P') => Ff; apply: cvg_trans; last exact: Ff.
rewrite /= /evaluator_dep=> Q /=; rewrite {1}/nbhs /=.
move=> [W nbdW <-]; rewrite /nbhs /=.
by (apply: filterS; last exact: nbdW) => g Wg /=; exists g. 
Qed.

Lemma hausdorff_pointwise : 
  (forall x, hausdorff (K x)) -> hausdorff (@product_topologicalType X K).
Proof.
move=> hsdfV => p q /= clstr.
apply: functional_extensionality_dep => x; apply: hsdfV.
move: clstr; rewrite ?cluster_cvgE /= => [[G PG [GtoQ psubG]]].
exists (evaluator_dep x @ G); first exact: fmap_proper_filter; split.
- rewrite -(evaluator_depE x).
  apply: cvg_trans; last apply: (@evaluator_dep_continuous x q).
  by apply: cvg_app; exact GtoQ.
- move/(cvg_app (evaluator_dep x)):psubG => xpsubxG.
  apply: cvg_trans; first exact: xpsubxG.
  by apply: evaluator_dep_continuous.
Qed.

End Evaluators.

Definition locally_compact (X : topologicalType) :=
    forall (x:X), exists2 U, compact U & nbhs x U.

Section Ascoli.
Context {X : topologicalType}.

Definition precompact {X : topologicalType} (C: set X) := 
  compact (closure C).


Lemma precompact_subset (A B: set X) : A `<=` B -> precompact B -> precompact A.
Proof.
move=> AsubB precompactB.
apply: (subclosed_compact (B := closure B)) => //.
- exact: closed_closure.
- exact: closure_subset.
Qed.
  
Context {Y : uniformType}.
Context {hsdf : hausdorff Y}.

Definition pointwisePrecomact (W : set (X -> Y)):=
  forall x, precompact [set (f x) | f in W].

Lemma pointwisePrecompact_precompact  (W : set ({ptws, X -> Y})):
  pointwisePrecomact W -> precompact W.
Proof.
move=> ptwsPreW; set K := fun x => closure [set f x | f in W].
set R := [set f : {ptws, X -> Y} | forall x : X, K x (f x)].
have C : compact R by apply: tychonoff => x; apply: ptwsPreW => //.
apply: subclosed_compact.
+ apply: closed_closure.
+ exact: C.
+ set L := (x in _`<=` x).
  have WsubR : W `<=` L. {
    rewrite /R/K => f /= Wf x; rewrite /K closure_limit_point /=.
    by left => /=; exists f; tauto.
  }
  have cR : closed R by apply: compact_closed => //; apply: hausdorff_pointwise.
  by rewrite closureE /= => q /=; apply; split => //.
Qed.
  
Lemma nbhs_entourage_ptws (f : {ptws, X -> Y}) x B : 
  entourage B -> nbhs f (fun g : {ptws, X -> Y} => B (g x, f x)).
Proof.
move=> entB; apply: nbhs_comp => //=.
- move => t _; apply: cvg_pair => //=; first by apply: nbhs_filter.
  + exact: evaluator_dep_continuous.
  + by apply: cvg_cst; apply: nbhs_filter.
- set C := (split_ent B); have entC: entourage C by exact: entourage_split_ent.
  have entCinv: entourage (C^-1)%classic by exact: entourage_inv.
  exists (to_set ((C^-1)%classic) (f x), to_set C (f x)) => //=.
  + split => //=; exact: (@nbhs_entourage _ _ ((C^-1)%classic)).
  + move=> v [/=X1 X2]; rewrite [v]surjective_pairing.
    by apply: entourage_split => //=; first apply: X1.
Qed.

Lemma closure_equicontinuous  (W : set ({ptws, X -> Y})):
  equicontinuous W -> equicontinuous (closure W) .
Proof.
move=> ectsW x0 E entE.
set A := (split_ent E); have entA: entourage A by exact: entourage_split_ent.
set B := (split_ent A); have entB: entourage B by exact: entourage_split_ent.
move: (ectsW x0 B entB) => [U [nbdU eqctsU]]; exists U; split => // g x cWf Ux.
set R := [set h : {ptws, X -> Y} | B (h x, g x) /\ A (g x0, h x0) ].
have nR: nbhs (g : {ptws, X -> Y}) R. {
  apply: filterI => //.
  - exact: nbhs_entourage_ptws.
  - under eq_fun => h do
      (rewrite (_: A (g x0, h x0) = (A^-1)%classic (h x0, g x0)); last by []).
    by apply: nbhs_entourage_ptws; exact: entourage_inv.
} 
move: (cWf R nR) => [h /= [Wh [Ah Bh]]]. 
apply: entourage_split => //; first by apply: Bh.
apply: entourage_split => //; last by apply: Ah.
exact: eqctsU.
Qed.

Lemma equicontinuous_cts (W : set (X -> Y)) f: 
  equicontinuous W -> W f -> continuous f.
Proof. 
  move=> ectsW Wf x; apply/cvg_entourageP => E entE.
  case: (ectsW x _ entE) => U [nbhsU Ef]; near_simpl; near=> y.
  by apply: Ef => //; apply (near nbhsU).
Grab Existential Variables. end_near. Qed.

Lemma equicontinuous_subset (W V : set (X -> Y)): 
  W `<=` V -> equicontinuous V -> equicontinuous W.
Proof. 
  move=> WsubV + x E entE => /(_ x E entE) [U [? Ef]].
  by exists U; split => // f y Wy Uy; apply Ef => //; apply WsubV.
Qed.

Lemma ptws_compact_cvg (W : set ({ptws, X -> Y})) F f:
  equicontinuous W -> 
  ProperFilter F -> 
  F W -> 
  {ptws, F --> f} = {family compact, F --> f}.
Proof.
move=> + PF; wlog Wf : f W / W f. {
  move=> + /closure_equicontinuous ectsCW FW => /(_ _ _ _ ectsCW) H. 
  rewrite propeqE; split; last by apply ptws_cvg_compact_family.
  move=> Ftof; rewrite -H //. 
  - by rewrite closureEcvg; exists F; tauto.
  - by apply: (filterS _ FW); rewrite closure_limit_point=>?; left.
} 
move=> ectsW FW; rewrite propeqE; split; last exact: ptws_cvg_compact_family. 
move=> ptwsF; apply/fam_cvgP => A cptA.
apply/cvg_restricted_entourageP => E1 entE1.
set E2 := (split_ent E1); have entE2: entourage E2 by 
    exact: entourage_split_ent.
set E3 := (split_ent E2); have entE3: entourage E3 by 
    exact: entourage_split_ent.
set E4 := E3 `&` (E3 ^-1)%classic; have entE4 : entourage E4 by
  apply: filterI => //; exact: entourage_inv.
rewrite compact_cover cover_compactE /= in cptA.
have mkR: forall x, exists R, open_nbhs x R /\ 
        (forall (y:X) (q : X -> Y), W q -> R y -> E4(q x, q y)). {
    move=> x; move: (ectsW x E4 entE4) => [R' [+ R'E]].
    rewrite nbhsE /= => [[R [onbhsR RsubR']]].
    exists R; split => // y q Wq Ry /=; apply: R'E => //.
    exact: RsubR'. 
}
set Rnbhd := fun (x : X) => A `&` projT1 (cid (mkR x)).
move/(_ X A Rnbhd): cptA.
pull1. {
  rewrite /open_fam_of; exists (fun x => projT1 (cid (mkR x))).
  - move=> x Ax; rewrite /Rnbhd /=; set R := cid _; case R => /=.
    move=> R'; rewrite open_nbhsE; tauto.
  - by [].
}
pull1. {
  rewrite /Rnbhd.
  move=> x Ax /=; exists x => //; split => //.
  set R := cid _; case R => /= R' [? ?]; apply nbhs_singleton.
  exact: open_nbhs_nbhs.
}
move=> [D' D'subA AsubRnbhd].
have Fx0: F (\bigcap_( x0 in [set x0 | x0 \in D']) [set q | E4(f x0, q x0)]). {
  apply: filter_bigI => x0 x0D'. 
  move/cvg_sup/(_ x0):ptwsF; rewrite /ptws_fun; apply => /=.
  move: (nbhs_entourage (f x0) entE4).
  rewrite nbhsE /= => [[B [onbhsB BsubE4]]].
  exists [set q | B (q x0)];split;[|split] => //=.
  - exists B; first by case: onbhsB.
    by [].
  - by apply: nbhs_singleton; apply: open_nbhs_nbhs.
  - by move=> q /= Bq; apply BsubE4.
}

near=> q => t At; have Wq: W q by apply: (near FW).
case /(_ t At) : AsubRnbhd => x0 /= xD' Rx0t.
have E4q : E4(q x0, q t). {
  move: Rx0t;rewrite /Rnbhd /= => [[_ ]]; set R' := cid _; case R' => /=.
  move=> R; rewrite open_nbhsE => [[[oR nbhsR] /(_ t q) ]] + Rt; apply => //.
}
have E4f : E4(f t, f x0). {
  move: Rx0t;rewrite /Rnbhd /= => [[_ ]]; set R' := cid _; case R' => /=.
  move=> R; rewrite open_nbhsE /E4 => [[[oR nbhsR] /(_ t f) ]] + Rt. 
  by do 2 (pull1 => //);  move=> E4f; split; apply E4f => //.
}
have E4subE3: E4 `<=` E3 by rewrite /E4 => ? [] //=.
do 2 (apply: entourage_split; first by []); apply: E4subE3; first exact: E4f; last exact: E4q.
  by exact: entourage_refl.
by have := (near Fx0 q); (pull1; first by done); apply.
Grab Existential Variables. end_near. Qed.    

Lemma ascoli_forward (W : (set (X -> Y))): 
  pointwisePrecomact W -> 
  equicontinuous W -> 
  @precompact [topologicalType of {family compact, X -> Y }] W.
Proof.
move=> /pointwisePrecompact_precompact + ectsW.
rewrite /precompact compact_ultra compact_ultra. 
have -> :@closure ([topologicalType of {family compact, X -> Y}]) W =
             @closure ([topologicalType of {ptws, X -> Y}]) W. {
  rewrite ?closureEcvg; rewrite predeqE => g /=.
  split; move => [F [PF [FW ?]]]; exists F.
  - by rewrite (ptws_compact_cvg (W:=W)).
  - by rewrite -(ptws_compact_cvg (W:=W)).
}
move=> /= + F UF FcW => /(_ F UF FcW); case=> p [cWp Fp]; exists p.
split=> //=.
rewrite -(ptws_compact_cvg (W:=(@closure [topologicalType of {ptws, X -> Y}] W))) => //.
exact: closure_equicontinuous.
Qed.


Lemma compact_equicontinuous (W : (set (X -> Y))) :
  locally_compact X -> 
  hausdorff X -> 
  (forall f, W f -> continuous f) ->
  @precompact [topologicalType of {family compact, X -> Y}] W -> 
  equicontinuous W.
Proof.
  move=> locCptX hsdfX ctsW cptW => x E1 entE1.  
  case/(_ x) : locCptX => B cptB nbhsB.
  set E2 := (split_ent E1); have entE2: entourage E2 by 
      exact: entourage_split_ent.
  set E3 := (split_ent E2); have entE3: entourage E3 by 
      exact: entourage_split_ent.
  set E4 := E3 `&` (E3 ^-1)%classic; have entE4 : entourage E4 by
      apply: filterI => //; exact: entourage_inv.
  set E5 := (split_ent E4); have entE5: entourage E5 by 
      exact: entourage_split_ent.
  set E6 := E5 `&` (E5 ^-1)%classic; have entE6 : entourage E6 by
      apply: filterI => //; exact: entourage_inv.
  have E3subE2 : E3 `<=` E2.
    move=>[??] ?; apply: entourage_split => //; eauto; exact: entourage_refl.
  have E4subE3 : E4 `<=` E3 by move =>? [] //.
  have E4invsubE3 : (E4 ^-1)%classic `<=` E3 by move=> [p q []/=]. 
  set cptTop := [topologicalType of {family compact, X -> Y}].
  set R1 := fun f => [set h : cptTop | forall y, B y -> E4 (f y, h y)]^°.
  set R := fun f => @closure cptTop W `&` R1 f.
  rewrite /precompact compact_cover cover_compactE  /= in cptW.
  move/(_ [choiceType of {family compact, X -> Y}] (@closure cptTop W) R): cptW.
  pull1. {
      exists R1.
      - by move=> f Wf /=; exact: open_interior.
      - by move=> ??; rewrite /R //=.
  }
  pull1. {
    move=> h Wh; exists h => //; rewrite /R/R1; split => //.
    rewrite /interior. 
    have FNh : Filter (nbhs h) by exact: nbhs_filter h.
    case: (@fam_cvgP X Y compact (nbhs h) h FNh) => + _.
    pull1; first exact:cvg_id; move/(_ (fun x => `[<B x>])).
    set B' := (x in compact x). have -> : B' = B  by 
        rewrite /B' funeqE=> z; rewrite asboolE.
    pull1; first by [].
    move/cvg_restricted_entourageP/(_ _ entE4).
    rewrite /cptTop near_simpl => [[Q [Q1 [Q2 Q3]]]].
    exists Q; (do 2 split=> //); move=> // t /= Qt y By; apply: Q3 =>//.
    by rewrite asboolE.
  }
  move=> [D DsubW Dcovers].
  set U := \bigcap_(g in [set i | i \in D]) [set y | E4 (g x, g y)].
  exists (U `&` B); split.
  - apply: filterI => //; apply: filter_bigI => g Dg.
    apply: nbhs_comp. 
    + move=> h; rewrite inE /= => Eh; apply: cvg_pair; first exact: cvg_cst.
      admit.
    + exists (to_set E6 (g x), to_set E6 (g x)) => /=; first split; 
        try (by apply: nbhs_entourage).
      move=> [p q] [/=] P Q; apply: (entourage_split (g x)) => //. 
      * by move: P => [].
      * by move: Q => [].
  - move=> f y Wf Uy; case: (Dcovers _ Wf)=> /= f0.
    rewrite /R/R1 => f0D [_ /interior_subset /= E4f].
    apply: (entourage_split (f0 y)) => //; last by 
      apply E3subE2, E4subE3, E4f, Uy.
    apply: (entourage_split (f0 x)) => //; first by 
      apply E4invsubE3, E4f, nbhs_singleton.
    apply E4subE3; by case: Uy=> [/(_ _ f0D) /= ].
Qed.

Lemma compact_pointwisePrecompact (W : set(X -> Y)): 
  hausdorff X -> 
  @compact [topologicalType of {family compact, X -> Y}] W -> 
  pointwisePrecomact W.
Proof.
  move=> hsdfX cptFamW x.
  have: @compact [topologicalType of {ptws, X -> Y}] W. {
    rewrite compact_ultra /= => F UF FW. 
    move: cptFamW; rewrite compact_ultra=> /(_ F UF FW) [h [Wh Fh]].
    exists h; split => //.
    by move=> /= Q Fq; apply: ptws_cvg_compact_family; first exact: Fh.
  }
  move/(continuous_compact (f := evaluator_dep x)).
  set C := (x in compact x).
  pull1; first ((move=> + _); apply: evaluator_dep_continuous). 
  move=> cptC; rewrite /precompact. 
  rewrite -(_ : [set f x | f in W] = closure [set f x | f in W] ) //.
  apply closure_id; apply: compact_closed => //.
Qed.

Lemma ArzelaAscoli (W : (set ({family compact, X -> Y}))) : 
  locally_compact X ->
  hausdorff X ->
  (equicontinuous W /\ pointwisePrecomact W) <->
  (@precompact [topologicalType of {family compact, X -> Y}] W /\ 
    (forall f, W f -> continuous f)).
Proof.
move=> lcptX hsdfX; split.
- case => ectsW ?; split; first apply: ascoli_forward => //.
  by move=> ? ?; apply: equicontinuous_cts; eauto.
- case=> cptWcl ctsW; split.
  + apply: equicontinuous_subset; first exact: 
      (subset_closure (T:= [topologicalType of {family compact, X -> Y}])). 
    apply: (compact_equicontinuous) => //.
    move=> f cFamWf; apply: (equicontinuous_cts ( W := @closure [topologicalType of {ptws, X -> Y}] W)).
    * apply: equicontinuous_subset.
    apply: compact_equicontinuous => //.
End Ascoli.