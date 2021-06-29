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
Section fct_Uniform.

Variable (T : choiceType) (U : uniformType).

Definition fct_ent :=
  filter_from
  (@entourage U)
  (fun P => [set fg | forall t : T, P (fg.1 t, fg.2 t)]).

Lemma fct_ent_filter : Filter fct_ent.
Proof.
apply: filter_from_filter; first by exists setT; apply: filterT.
move=> A B entA entB.
exists (A `&` B); first exact: filterI.
by move=> fg ABfg; split=> t; have [] := ABfg t.
Qed.

Lemma fct_ent_refl A : fct_ent A -> [set fg | fg.1 = fg.2] `<=` A.
Proof.
move=> [B entB sBA] fg feg; apply/sBA => t; rewrite feg.
exact: entourage_refl.
Qed.

Lemma fct_ent_inv A : fct_ent A -> fct_ent (A^-1)%classic.
Proof.
move=> [B entB sBA]; exists (B^-1)%classic; first exact: entourage_inv.
by move=> fg Bgf; apply/sBA.
Qed.

Lemma fct_ent_split A : fct_ent A -> exists2 B, fct_ent B & B \o B `<=` A.
Proof.
move=> [B entB sBA].
(* have Bsplit : exists C, entourage C /\ C \o C `<=` B. *)
(*   exact/exists2P/entourage_split_ex. *)
exists [set fg | forall t, split_ent B (fg.1 t, fg.2 t)].
  by exists (split_ent B).
move=> fg [h spBfh spBhg].
by apply: sBA => t; apply: entourage_split (spBfh t) (spBhg t).
Qed.

Definition fct_uniformType_mixin :=
  UniformMixin fct_ent_filter fct_ent_refl fct_ent_inv fct_ent_split erefl.

Definition fct_topologicalTypeMixin :=
  topologyOfEntourageMixin fct_uniformType_mixin.

Canonical generic_source_filter := @Filtered.Source _ _ _ (nbhs_ fct_ent).
Canonical fct_topologicalType :=
  TopologicalType (T -> U) fct_topologicalTypeMixin.
Canonical fct_uniformType := UniformType (T -> U) fct_uniformType_mixin.

End fct_Uniform.

Section fct_PseudoMetric.
Variable (T : choiceType) (R : numFieldType) (U : pseudoMetricType R).
Definition fct_ball (x : T -> U) (eps : R) (y : T -> U) :=
  forall t : T, ball (x t) eps (y t).
Lemma fct_ball_center (x : T -> U) (e : R) : 0 < e -> fct_ball x e x.
Proof. by move=> /posnumP[{}e] ?. Qed.

Lemma fct_ball_sym (x y : T -> U) (e : R) : fct_ball x e y -> fct_ball y e x.
Proof. by move=> P t; apply: ball_sym. Qed.
Lemma fct_ball_triangle (x y z : T -> U) (e1 e2 : R) :
  fct_ball x e1 y -> fct_ball y e2 z -> fct_ball x (e1 + e2) z.
Proof. by move=> xy yz t; apply: (@ball_triangle _ _ (y t)). Qed.
Lemma fct_entourage : entourage = entourage_ fct_ball.
Proof.
rewrite predeqE => A; split; last first.
  by move=> [_/posnumP[e] sbeA]; exists [set xy | ball xy.1 e%:num xy.2].
move=> [P]; rewrite -entourage_ballE => -[_/posnumP[e] sbeP] sPA.
by exists e%:num => // fg fg_e; apply: sPA => t; apply: sbeP; apply: fg_e.
Qed.
Definition fct_pseudoMetricType_mixin :=
  PseudoMetricMixin fct_ball_center fct_ball_sym fct_ball_triangle fct_entourage.
Canonical fct_pseudoMetricType := PseudoMetricType (T -> U) fct_pseudoMetricType_mixin.
End fct_PseudoMetric.

Lemma cvg_fct_entourageP (T : choiceType) (U : uniformType)
  (F : set (set (T -> U))) (FF : Filter F) (f : T -> U) :
  F --> f <->
  forall A, entourage A ->
  \forall g \near F, forall t, A (f t, g t).
Proof.
split.
  move=> /cvg_entourageP Ff A entA.
  by apply: (Ff [set fg | forall t : T, A (fg.1 t, fg.2 t)]); exists A.
move=> Ff; apply/cvg_entourageP => A [P entP sPA]; near=> g.
by apply: sPA => /=; near: g; apply: Ff.
Grab Existential Variables. all: end_near. Qed.
(* Special notation for functions, considered as converging uniformly
   over their whole domain *)

Section fun_Complete.

Context {T : choiceType} {U : completeType}.

Lemma fun_complete (F : set (set (T -> U)))
  {FF :  ProperFilter F} : cauchy F -> cvg F.
Proof.
move=> Fc.
have /(_ _) /cauchy_cvg /cvg_app_entourageP cvF : cauchy (@^~_ @ F).
  move=> t A /= entA; rewrite near_simpl -near2E near_map2.
  by apply: Fc; exists A.
apply/cvg_ex; exists (fun t => lim (@^~t @ F)).
apply/cvg_fct_entourageP => A entA; near=> f => t; near F => g.
apply: (entourage_split (g t)) => //; first by near: g; apply: cvF.
move: (t); near: g; near: f; apply: nearP_dep; apply: Fc.
exists ((split_ent A)^-1)%classic=> //=.
by apply: entourage_inv; apply: entourage_split_ent.
Grab Existential Variables. all: end_near. Qed.

Canonical fun_completeType := CompleteType (T -> U) fun_complete.

End fun_Complete.


Canonical fct_completePseudoMetricType (T : choiceType) (R : numFieldType)
  (U : completePseudoMetricType R) :=
  CompletePseudoMetricType (T -> U) fun_complete.
Section Restrictions.
Context {U: Type} (A : set U).

Definition patch {V} (f g : U -> V) u :=
  if u \in A then g u else f u.

Local Notation restrict := (fun f => patch (fun=> point) f).

Definition fun_eq_on {V} (f : U -> V) (g : U -> V) : Prop :=
  forall y, A y -> f y = g y.
Context {V : pointedType}.

Definition restrict_dep (f : U -> V) (u : { x : U | x \in A }): V :=
  f (projT1 u). 

Definition extend_dep (f : {x | x \in A } -> V) (u : U) :=
  if pselect (u \in A) is left w then f (exist _ u w) else point.


Open Scope fun_scope.
Lemma extend_restrict_dep :
  (@extend_dep) \o (restrict_dep) = restrict.
Proof.
rewrite funeq2E => f u /=; rewrite /restrict_dep /restrict /extend_dep /patch.
by case: pselect => [/= ->//|/negP/negbTE ->].
Qed.

Lemma restrict_extend_dep f: (restrict_dep (extend_dep f)) = f.
Proof.
rewrite funeqE => u.
rewrite /restrict_dep /restrict /extend_dep /patch /=; case: pselect.
- by move=> Au; f_equal; destruct u; apply exist_congr.
- by move=> Q; contradict Q; destruct u.
Qed.

Lemma restrict_dep_restrict : restrict_dep \o restrict = restrict_dep.
Proof.
rewrite funeq2E => f -[u Au] /=.
by rewrite /restrict_dep /restrict /extend_dep /patch /= Au.
Qed.

Lemma restrict_dep_setT : [set of restrict_dep] = setT.
Proof.
  rewrite eqEsubset; split => //= f _; exists (extend_dep f)=>//.
  exact: restrict_extend_dep.
Qed.

Program Definition forall_sigP_def  (P : {x | x \in A} -> Prop):= 
  (forall u : {x | x \in A}, P u) = 
  (forall u : U, forall (a:A u), P (exist _ u _)).
Next Obligation.  by rewrite inE. Qed.

Lemma forall_sigP  (P : {x | x \in A} -> Prop) : forall_sigP_def P.
Proof.
rewrite /forall_sigP_def; rewrite propeqE; split => Pu.
- move=> u ?; have Au : (u \in A) by rewrite in_setE. 
  rewrite [exist _ _ _](_ : _ = exist _ u Au); first exact: Pu.
  exact: exist_congr.
- move=> [u ?]; have Au : (A u) by rewrite -in_setE.
  by move: (Pu u Au); apply ssr_congr_arrow, f_equal, exist_congr.
Qed.
End Restrictions.

Local Notation restrict := (fun A f => patch A (fun=> point) f).
Arguments restrict_dep {U} (A) {V} (f).
Arguments extend_dep {U} {A} {V} (f).

Section RestrictedTopology.
Context {U : choiceType} (A : set U) {V : uniformType} .

Definition fct_RestrictedUniform := let _ := A in U -> V.
Definition fct_RestrictedUniformTopology := 
  @weak_topologicalType 
    ([pointedType of @fct_RestrictedUniform])
    (fct_uniformType [choiceType of { x : U | x \in A }] V) (@restrict_dep U A V).

Canonical fct_RestrictUniformFilteredType:=
  [filteredType fct_RestrictedUniform of 
      fct_RestrictedUniform for 
      fct_RestrictedUniformTopology].
Canonical fct_RestrictUniformTopologicalType :=
  [topologicalType of fct_RestrictedUniform for 
      fct_RestrictedUniformTopology].

Lemma restricted_nbhs (f : fct_RestrictedUniformTopology) P: 
  nbhs f P <-> (exists E, entourage E /\ 
    [set h | forall y, A y -> E(f y, h y)] `<=` P).
Proof.
split.  
- move=> [Q [[/= W oW <- /=] [Wf subP]]].
  rewrite openE /= /interior in oW.
  case: (oW _ Wf) => ? [ /= E entE] Esub subW.
  exists E; split => // h Eh; apply subP, subW, Esub => /= [[u Au]].
  by apply: Eh => /=; rewrite -inE.
- case=> E [entE subP]; apply: (filterS subP).
  apply : (filterS  (P := 
      [set h | forall y, E (restrict_dep A f y, restrict_dep A h y)])).
  + move=> g /= + y Ay => /( _ (exist (fun x => x \in A) y _)) /=; apply.
    by rewrite inE.
  + move: (cvg_image (f := restrict_dep A) f (nbhs_filter f) 
                     (restrict_dep_setT _ )).
    case => /(_ cvg_id) + _ => /(_ 
       [set h | forall y, E (restrict_dep A f y, h y)]) /=.
    case; first by exists [set fg | forall y, E (fg.1 y, fg.2 y)]; [exists E|].
    move=> B nbhsB rBrE.
    apply: (filterS _ nbhsB) => g Bg /= [y yA /=].
    by move: rBrE; rewrite eqEsubset; case => [+ _]; apply; exists g.
Qed.

Definition fct_restrict_ent :=
  filter_from
  (@entourage V)
  (fun P => [set fg | forall t : U, A t -> P (fg.1 t, fg.2 t)]).
Program Definition restrict_uniform_mixin := 
  @Uniform.Mixin (fct_RestrictedUniform) (fun f => nbhs f) (fct_restrict_ent)
   _ _ _ _ _.

Next Obligation.
apply: filter_from_filter; first by exists setT; apply: filterT.
move=> P Q entP entQ.
exists (P `&` Q); first exact: filterI.
by move=> [f g /=] ABfg; split=> t At; have [] := ABfg t.
Qed.

Next Obligation.
move=> [?? /=] ->.
by case: H => E entE; apply => /=??; exact: entourage_refl.
Qed.

Next Obligation.
case: H => E entE Esub; exists (E^-1)%classic; first exact: entourage_inv.
by move=> [??/=] ?; apply: Esub.
Qed.

Next Obligation.
case: H => E entE Esub. 
exists [set fg | forall y, A y -> split_ent E (fg.1 y, fg.2 y)]. 
- by exists (split_ent E) => //. 
- move=>[??/=] [g Eag Egb]; apply: Esub => /= t At. 
  by apply: entourage_split => //;[exact: Eag| exact: Egb].
Qed.

Next Obligation.
rewrite funeq2E => f P /=; move: (restricted_nbhs f P); rewrite -propeqE => ->.
rewrite propeqE; split; move=> [E].
- move=> [entE EsubP]; exists [set fg | forall y, A y -> E (fg.1 y, fg.2 y)].
  + exists E => //.
  + exact: EsubP.
- move=> [E' entE' E'subE EsubP].
  by exists E'; split => // h E'h; apply EsubP, E'subE.
Qed.

Canonical fct_restrictedUniformType := 
  UniformType (fct_RestrictedUniform) restrict_uniform_mixin.

Lemma restricted_cvgP (F : set(set(U -> V))) (f : fct_RestrictedUniform) : 
  Filter F ->
  (F --> f) <-> (forall E, entourage E -> \near F, (forall y, A y -> E (f y, F y))).
Proof.
move=> FF; split.
- move=> + E entE; apply; apply/restricted_nbhs; exists E; split => //.
  by move=> ?.
- move=> Ef => Q /restricted_nbhs [E [entE subQ]].
  by apply: (filterS subQ); apply Ef.
Qed.


End RestrictedTopology.

Ltac pull1 :=
  match goal with
  | |- (?x -> _) -> _ => let Q := fresh in 
    have Q : x; last move=>/(_ Q)
  end.
(* We use this function to help coq identify the correct notation to use
   when printing. Otherwise you get goals like `F --> f -> F --> f`      *)
Definition restrict_fun {U : choiceType} A (V : uniformType)
  (f : U -> V) : @fct_RestrictedUniform U A V := f.

Notation "'{uniform' A -> V }" := (@fct_RestrictedUniform _ A V) : classical_set_scope.

Notation "'{uniform' A , F --> f }" :=
  (F --> (restrict_fun A f)) : classical_set_scope.

Lemma restricted_cvgE {U : choiceType} {V : uniformType}
    (F : set (set (U -> V))) A (f : U -> V) :
  {uniform A, F --> f} = (F --> (f : @fct_RestrictedUniform U A V)).
Proof. by []. Qed.

Definition fct_Pointwise U (V: topologicalType):= U -> V.

Definition fct_PointwiseTopology (U : Type) (V : topologicalType) := 
  @product_topologicalType U (fun=> V).

Canonical fct_PointwiseFilteredType (U : Type) (V : topologicalType) :=
  [filteredType @fct_Pointwise U V of
     @fct_Pointwise U V for 
     @fct_PointwiseTopology U V].
Canonical fct_PointwiseTopologicalType (U : Type) (V : topologicalType) :=
  [topologicalType of 
     @fct_Pointwise U V for 
     @fct_PointwiseTopology U V].

Notation "'{ptws' U -> V }" := (@fct_Pointwise U V).
Definition ptws_fun {U : Type} {V : topologicalType}
  (f : U -> V) : {ptws U -> V} := f.

Notation "'{ptws' F --> f }" := 
    (F --> (@ptws_fun _ _ f)) : classical_set_scope. 

Lemma ptws_cvgE {U : Type} {V : topologicalType}
    (F : set (set(U -> V))) (A : set U) (f : U -> V) :
  {ptws F --> f} = (F --> (f : {ptws U -> V})).
Proof. by []. Qed.

Section UniformCvgLemmas.
Context {U : choiceType} {V : uniformType}.

Lemma ptws_uniform_cvg  (f : U -> V) (F : set (set (U -> V))) : 
  Filter F -> {uniform setT, F --> f} -> {ptws F --> f}.
Proof.
move=> FF; rewrite cvg_sup => W i.
rewrite cvg_image; last by rewrite eqEsubset; split=> v // _; exists (cst v).
move=> C /=; rewrite -nbhs_entourageE nbhs_filterE => -[B eB BsubC].
suff sub2 : @^~ i @` [set g | forall u, B (f u, g u)] `<=` to_set B (f i).
set l := (x in x _); suff weakL : forall X Y, X `<=` Y -> l X -> l Y.
apply: (weakL _ _ (subset_trans sub2 BsubC)).
- exists [set g : U -> V | forall u, B (f u, g u)] => //.
  apply W => /=. apply/restricted_nbhs; eexists; split; first by exact: eB. 
  by move=> ? Q ? //=; apply Q.
- move=> X Y /setUidPl XsubY [P FP EX].
  exists ( P `|` [set g : U -> V | exists v, Y v /\ g = cst v]).
    by apply: (@filterS _ _ _ P) => //= t ?; left.
  rewrite image_setU EX setUC [x in x `|` _](_ : _ = Y) // eqEsubset; split.
  * by move => t /= [/= h [/= v [? ->] <-]].
  * by move => t ?; exists (cst t) => //; exists t.
- by move => v [/= g] + <-; apply.
Qed.

Lemma fun_eq_onP (f g : U -> V) (A : set U) :
  fun_eq_on A f g <-> restrict_dep A f = restrict_dep A g.
Proof.
rewrite /fun_eq_on; split=> [eq_f_g | Rfg u uA].
- rewrite funeqE /restrict_dep => [[??]]; rewrite eq_f_g //.
  by set u := (x in projT1 x); case u=> //= ?; rewrite inE.
- rewrite -inE in uA.
  rewrite (_ : f u = restrict_dep A f (exist _ u uA)) //.
  rewrite (_ : g u = restrict_dep A g (exist _ u uA)) //.
  by move: Rfg; rewrite funeqE; apply.
Qed.

Lemma cvg_restrict_dep (A : set U) (f : U -> V) (F : set (set (U -> V))) : Filter F ->
  {uniform A, F --> f} <-> {uniform setT, restrict_dep A @ F --> (restrict_dep A f)}.
Proof.
move=> FF; split.
- move=> cvgF P' /= /restricted_nbhs [ E [/= entE EsubP]].
  apply: (filterS EsubP); apply: cvgF => /=.
  apply: (filterS ( P:= [set h | forall y, A y -> E(f y, h y)])).
    + by move=> h/= Eh [y ?] _; apply Eh; rewrite -inE.
    + by (apply/restricted_nbhs; eexists; split; eauto).
- move=> cvgF P' /= /restricted_nbhs [ E [/= entE EsubP]].
  apply: (filterS EsubP).
  move: (cvgF  [set h | (forall y , E (restrict_dep A f y, h y))]) => /=.
  set Q := (x in (_ -> x) -> _); move=> W.
  have: Q by apply W, restricted_nbhs; exists E; split => // h + ?; apply.
  rewrite {}/W {}/Q; near_simpl => /= R; apply: (filterS _ R) => h /=.
  by rewrite forall_sigP /restrict_dep /=.
Qed.

Lemma eq_on_close (A : set U) (f g : {uniform A -> V}) :
  fun_eq_on A f g -> close f g.
Proof.
rewrite entourage_close => eqfg ? [E entE]; apply => t At /=.
by rewrite eqfg //; exact: entourage_refl.
Qed.

Lemma hausdorrf_close_eq_on (A : set U) (f g : {uniform A -> V}) :
  hausdorff V -> (close f g = fun_eq_on A f g).
Proof.
move=> hV.
rewrite propeqE; split; last exact: eq_on_close.
rewrite entourage_close => C u uA; apply: hV.
rewrite /cluster -nbhs_entourageE /= => X Y [X' eX X'X] [Y' eY Y'Y].
exists (g u); split; [apply: X'X| apply: Y'Y]; last exact: entourage_refl.
apply: (C [set fg | forall y, A y -> X' (fg.1 y, fg.2 y)]) => //=.
exists X' => //=.
Qed.

Lemma restricted_subset_nbhs (f : U -> V) (A B : set U) :
  B `<=` A -> nbhs (f : {uniform A -> V}) `=>` nbhs (f : {uniform B -> V}).
Proof.
move => BsubA P /restricted_nbhs [E [entE EsubP]].
apply: (filterS EsubP); apply/restricted_nbhs; exists E; split => //.
by move=> h Eh y /BsubA Ay; exact: Eh.
Qed.

Lemma restricted_subset_cvg (f : U -> V) (A B : set U) F :
  Filter F -> B `<=` A -> {uniform A, F --> f} -> {uniform B, F --> f}.
Proof.
move => FF /restricted_subset_nbhs => /(_ f); rewrite /restrict_fun.
move=> nbhsF Acvg; apply: cvg_trans; first exact: Acvg.
exact: nbhsF.
Qed.

Lemma restricted_restrict_cvg 
    (F : set (set (U -> V))) (f : U -> V) A : 
  Filter F ->
  {uniform A, F --> f} <-> {uniform setT, restrict A @ F --> restrict A f}.
Proof.
move=> FF; rewrite cvg_restrict_dep; split.
- rewrite -extend_restrict_dep /restrict_fun.
  move /(cvg_app (extend_dep (A:=A))) => D.
  apply: cvg_trans; first exact: D.
  move=> P /restricted_nbhs [E [/=entE EsubP]]; apply: (filterS EsubP).
  apply/restricted_nbhs; exists E; split=> //= h /=.
  rewrite /restrict_dep => R u _. 
  rewrite /extend_dep/patch; case pselect => //= Au. 
    by set u' := exist _ _ _; rewrite Au ( _: u = projT1 u') //; exact: R.
  by rewrite ifF; first exact: entourage_refl; apply/negP.
- move /(@cvg_app _ _ _ _ (restrict_dep A)).
  rewrite fmap_comp restrict_dep_restrict => D.
  apply: cvg_trans; first exact: D.
  move=> P /restricted_nbhs [E [/=entE EsubP]]; apply: (filterS EsubP).
  apply/restricted_nbhs; exists E; split=> //= h /=.
  rewrite /restrict_dep /restrict_fun => R [u Au] _ /=. 
  by move: (R u (ltac:(by []))); rewrite /patch Au.
Qed.

Lemma cvg_restrictedU (f : U -> V) (F : set (set (U -> V))) A B : Filter F ->
  {uniform A, F --> f} -> {uniform B, F --> f} ->
  {uniform (A `|` B), F --> f}.
Proof.
move=> FF AFf BFf Q /=/restricted_nbhs [E [entE EsubQ]].
apply: (filterS EsubQ); rewrite /restrict_fun.
rewrite (_:  [set h | (forall y : U, (A `|` B) y -> E (f y, h y))] = 
    [set h | forall y, A y -> E (f y, h y)] `&` 
    [set h | forall y, B y -> E (f y, h y)]).
- apply filterI; [apply: AFf| apply: BFf]. 
  + by apply/restricted_nbhs; exists E; split.
  + by apply/restricted_nbhs; exists E; split.
- rewrite eqEsubset; split=> h.
  + by move=> R; split=> t ?; apply R;[left| right].
  + by move=> [R1 R2] y [? | ?]; [apply R1| apply R2].
Qed.

Lemma cvg_restricted_set0 (F : set (set (U -> V))) (f : U -> V) : Filter F ->
  {uniform set0, F --> f}.
Proof.
move=> FF P /= /restricted_nbhs [E [? R]].
suff -> : P = setT by apply filterT.
rewrite eqEsubset; split => //=.
by apply: subset_trans R => g _ ?.
Qed.

Definition fct_UniformFamily (fam : (set U) -> Prop) := U -> V.

Definition family_cvg_topologicalType (fam : set U -> Prop) :=
  @sup_topologicalType _ (sigT fam)
  (fun k => Topological.class (@fct_restrictedUniformType U (projT1 k) V)).

Definition restrict_fam fam (f : U -> V) : fct_UniformFamily fam := f.

Canonical fct_UniformFamilyFilteredType fam :=
  [filteredType fct_UniformFamily fam of 
    fct_UniformFamily fam for 
    family_cvg_topologicalType fam].
Canonical fct_UniformFamilyTopologicalType fam :=
  [topologicalType of 
     fct_UniformFamily fam for 
     family_cvg_topologicalType fam].

Local Notation "'{family' fam , F --> f }" :=
  (F --> (restrict_fam fam f)) : classical_set_scope.

Lemma fam_cvgP (fam : set U -> Prop) (F : set (set (U -> V))) (f : U -> V) :
  Filter F -> {family fam, F --> f} <->
  (forall A : set U, fam A -> {uniform A, F --> f }).
Proof.
split; first by move=> /cvg_sup + A FA; move/(_ (existT _ _ FA)).
by move=> famFf /=; apply/cvg_sup => [[? ?] FA]; apply: famFf.
Qed.

Lemma fam_entourage_cvgP (fam : set U -> Prop) (F : set (set (U -> V))) (f : U -> V) :
  Filter F -> {family fam, F --> f} <->
  (forall (A : set U) E, fam A -> entourage E -> \near F, forall y, A y -> E (f y, F y) ).
Proof.
move=> FF; apply: iff_trans; first exact: fam_cvgP; split.
- by move=> + A + famA + => /(_ A famA)/restricted_cvgP .
- move=> Ff A famA; apply/restricted_cvgP => E entE. 
  exact: (Ff A E famA entE).
Qed.
  
Lemma family_cvg_subset (famA famB : set U -> Prop) (F : set (set (U -> V)))
    (f : U -> V) : Filter F ->
  famA `<=` famB -> {family famB, F --> f} -> {family famA, F --> f}.
Proof.
by move=> FF S /fam_cvgP famBFf; apply/fam_cvgP => A ?; apply/famBFf/S.
Qed.

(* TODO (zstone): integrate this into the compactness section *)
Definition finCover (I : choiceType) (F : I -> set U) (A : set U) :=
  exists D : {fset I}, A `<=` \bigcup_(i in [set i | i \in D]) F i.

Lemma family_cvg_finite_covers (famA famB : set U -> Prop)
  (F : set (set (U -> V))) (f : U -> V) : Filter F ->
  (forall P, famA P ->
    exists (I : choiceType) f, (forall i, famB (f i)) /\ @finCover I f P) ->
  {family famB, F --> f} -> {family famA, F --> f}.
Proof.
move=> FF ex_finCover /fam_cvgP rFf; apply/fam_cvgP => A famAA.
move: ex_finCover => /(_ _ famAA) [R [g [g_famB [D]]]].
move/restricted_subset_cvg; apply.
move: D; apply: finSet_rect => X IH.
have [/eqP ->|/set0P[x xX]] := boolP ([set i | i \in X] == set0).
  by rewrite bigcup_set0; apply: cvg_restricted_set0.
rewrite -(fsetD1K xX) bigcup_setU1; apply: cvg_restrictedU.
- exact/rFf/g_famB.
- exact/IH/fproperD1.
Qed.
End UniformCvgLemmas.

Notation "'{family' fam , U -> V }" :=  (@fct_UniformFamily U V fam).
Notation "'{family' fam , F --> f }" :=
  (F --> (restrict_fam fam f)) : classical_set_scope.

Lemma fam_cvgE {U : topologicalType} {V : uniformType} 
    (F : set (set (U -> V)))
    (f : U -> V) fam :
  {family fam, F --> f} = (F --> (f : {family fam, U -> V})).
Proof. by []. Qed.

Definition compactly_in {U : topologicalType} (A : set U) :=
  [set B | B `<=` A /\ compact B].

Lemma compact_cvg_within_compact {U : topologicalType} {V : uniformType}
    (C : set U) (F : set (set (U -> V))) (f : U -> V) :
  Filter F -> compact C ->
  {uniform C, F --> f} <-> {family (compactly_in C), F --> f}.
Proof.
move=> FF CC.
apply: (iff_trans _ (iff_sym (fam_cvgP _ _ FF))); split.
- by move=> CFf D [/restricted_subset_cvg + _]; apply.
- by apply; split.
Qed.

Definition singletons {X : Type} := [set P | exists (x:X), P = [set x]].

Lemma ptws_cvg_family_singleton {U : topologicalType} {V : uniformType} F (f: U -> V):
  Filter F ->
  {ptws F --> f} = {family (@singletons U), F --> f}.
Proof.
  move=> FF; rewrite propeqE fam_cvgP cvg_sup /ptws_fun; split.
  - move=> + A [x ->] => /(_ x) Ff; apply/restricted_cvgP => E entE.
    near=> q => t ->; near:q; apply: Ff => /=.
    move: (nbhs_entourage (f x) entE).
    rewrite nbhsE /= => [[B [onbhsB BsubE]]].
    exists [set q | B (q x)];split;[|split] => //=.
    + exists B; first by case: onbhsB.
      by [].
    + by apply: nbhs_singleton; apply: open_nbhs_nbhs.
    + by move=> q /= Bq; apply BsubE.
  - move=> + x => /(_ [set x]); pull1; first by exists x.
    move=> /restricted_cvgP Ef => /= P /= [P' [[A oA /= <- /=] [Afx AsubP]]].
    rewrite openE /interior in oA; case/nbhsP: (oA (f x) (Afx))=> E entE EsubA.
    move:(Ef _ entE) => EF.
    by near=> g; apply: AsubP; apply: EsubA; apply (near EF).
Grab Existential Variables. end_near. end_near. Qed.

Lemma ptws_cvg_compact_family {X : topologicalType} {Y : uniformType} F (f: X -> Y):
  ProperFilter F -> {family compact, F --> f} -> {ptws F --> f}.
Proof.
move=> PF; rewrite ptws_cvg_family_singleton; apply: family_cvg_subset.
move=> A [x ->]; apply: compact_singleton.
Qed.

(** ** Limit switching *)
Section Cvg_switch.
Context {T1 T2 : choiceType}.

Lemma cvg_switch_1 {U : uniformType}
  F1 {FF1 : ProperFilter F1} F2 {FF2 : Filter F2}
  (f : T1 -> T2 -> U) (g : T2 -> U) (h : T1 -> U) (l : U) :
  f @ F1 --> g -> (forall x1, f x1 @ F2 --> h x1) -> h @ F1 --> l ->
  g @ F2 --> l.
Proof.
move=> fg fh hl; apply/cvg_app_entourageP => A entA.
near F1 => x1; near=> x2; apply: (entourage_split (h x1)) => //.
  by near: x1; apply/(hl (to_set _ l)) => /=.
apply: (entourage_split (f x1 x2)) => //.
  by near: x2; apply/(fh x1 (to_set _ _)) => /=.
move: (x2); near: x1; have /cvg_fct_entourageP /(_ (_^-1%classic)):= fg; apply.
exact: entourage_inv.
Grab Existential Variables. all: end_near. Qed.

Lemma cvg_switch_2 {U : completeType}
  F1 {FF1 : ProperFilter F1} F2 {FF2 : ProperFilter F2}
  (f : T1 -> T2 -> U) (g : T2 -> U) (h : T1 -> U) :
  f @ F1 --> g -> (forall x, f x @ F2 --> h x) ->
  [cvg h @ F1 in U].
Proof.
move=> fg fh; apply: cauchy_cvg => A entA.
rewrite !near_simpl -near2_pair near_map2; near=> x1 y1 => /=; near F2 => x2.
apply: (entourage_split (f x1 x2)) => //.
  by near: x2; apply/(fh _ (to_set _ _)) => /=.
apply: (entourage_split (f y1 x2)) => //; last first.
  near: x2; apply/(fh _ (to_set ((_^-1)%classic) _)).
  exact: nbhs_entourage (entourage_inv _).
apply: (entourage_split (g x2)) => //; move: (x2); [near: x1|near: y1].
  have /cvg_fct_entourageP /(_ (_^-1)%classic) := fg; apply.
  exact: entourage_inv.
by have /cvg_fct_entourageP := fg; apply.
Grab Existential Variables. all: end_near. Qed.

Lemma cvg_switch {U : completeType}
  F1 (FF1 : ProperFilter F1) F2 (FF2 : ProperFilter F2)
  (f : T1 -> T2 -> U) (g : T2 -> U) (h : T1 -> U) :
  f @ F1 --> g -> (forall x1, f x1 @ F2 --> h x1) ->
  exists l : U, h @ F1 --> l /\ g @ F2 --> l.
Proof.
move=> Hfg Hfh; have hcv := !! cvg_switch_2 Hfg Hfh.
by exists [lim h @ F1 in U]; split=> //; apply: cvg_switch_1 Hfg Hfh hcv.
Qed.

End Cvg_switch.

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

Section Precompact.
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
End Precompact.
  
Section Arzela.
Context {X : topologicalType}.
Context {Y : uniformType}.
Context {hsdf : hausdorff Y}.

Definition pointwisePrecomact (W : set (X -> Y)):=
  forall x, precompact [set (f x) | f in W].

Lemma pointwisePrecompact_precompact  (W : set ({ptws X -> Y})):
  pointwisePrecomact W -> precompact W.
Proof.
move=> ptwsPreW; set K := fun x => closure [set f x | f in W].
set R := [set f : {ptws X -> Y} | forall x : X, K x (f x)].
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
  
Lemma nbhs_entourage_ptws (f : {ptws X -> Y}) x B : 
  entourage B -> nbhs f (fun g : {ptws X -> Y} => B (g x, f x)).
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

Lemma closure_equicontinuous  (W : set ({ptws X -> Y})):
  equicontinuous W -> equicontinuous (closure W) .
Proof.
move=> ectsW x0 E entE.
set A := (split_ent E); have entA: entourage A by exact: entourage_split_ent.
set B := (split_ent A); have entB: entourage B by exact: entourage_split_ent.
move: (ectsW x0 B entB) => [U [nbdU eqctsU]]; exists U; split => // g x cWf Ux.
set R := [set h : {ptws X -> Y} | B (h x, g x) /\ A (g x0, h x0) ].
have nR: nbhs (g : {ptws X -> Y}) R. {
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

Lemma pointwisePrecomact_subset (W V : set (X -> Y)): 
  W `<=` V -> pointwisePrecomact V -> pointwisePrecomact W.
Proof. 
  move=> WsubV + x => /(_ x) pcptV.
  apply: precompact_subset; last exact: pcptV.
  exact: image_subset.
Qed.

Lemma compact_cvg_nbhs (f : {family compact, X -> Y}) B E: 
  entourage E -> compact B ->
  nbhs f [set q | forall x, B x -> E (f x, q x)].
Proof.
move=> entE cptB.
have FNh : Filter (nbhs f) by exact: nbhs_filter f.
case: (@fam_cvgP X Y compact (nbhs f) f FNh) => + _.
pull1; first exact:cvg_id; move/(_ (fun x => `[<B x>])).
set B' := (x in compact x). have -> : B' = B  by 
    rewrite /B' funeqE=> z; rewrite asboolE.
pull1; first by [].
move/restricted_cvgP/(_ _ entE).
rewrite near_simpl => [[Q [Q1 [Q2 Q3]]]].
exists Q; (do 2 split=> //); move=> // t /= Qt y By; apply: Q3 =>//.
by rewrite asboolE.
Qed.

Lemma ptws_compact_cvg (W : set ({ptws X -> Y})) F f:
  equicontinuous W -> 
  ProperFilter F -> 
  F W -> 
  {ptws F --> f} = {family compact, F --> f}.
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
apply/restricted_cvgP => E1 entE1.
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
             @closure ([topologicalType of {ptws X -> Y}]) W. {
  rewrite ?closureEcvg; rewrite predeqE => g /=.
  split; move => [F [PF [FW ?]]]; exists F.
  - by rewrite (ptws_compact_cvg (W:=W)).
  - by rewrite -(ptws_compact_cvg (W:=W)).
}
move=> /= + F UF FcW => /(_ F UF FcW); case=> p [cWp Fp]; exists p.
split=> //=.
rewrite -(ptws_compact_cvg (W:=(@closure [topologicalType of {ptws X -> Y}] W))) => //.
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
  set E7 := (split_ent E6); have entE7: entourage E7 by 
      exact: entourage_split_ent.
  have E3subE2 : E3 `<=` E2 by
    move=>[??] ?; apply: entourage_split => //; eauto; exact: entourage_refl.
  have E4subE3 : E4 `<=` E3 by move =>? [] //.
  have E4invsubE3 : (E4 ^-1)%classic `<=` E3 by move=> [p q []/=]. 
  have E5subE4 : E5 `<=` E4 by
    move=>[??] ?; apply: entourage_split => //; eauto; exact: entourage_refl.
  have E6subE5 : E6 `<=` E5 by move=>?[].
  have E7subE6 : E7 `<=` E6 by
    move=>[??] ?; apply: entourage_split => //; eauto; exact: entourage_refl.
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
    exact: compact_cvg_nbhs.
  }
  move=> [D DsubW Dcovers].
  set U := \bigcap_(g in [set i | i \in D]) [set y | B y -> E4 (g x, g y)].
  exists (U `&` B); split.
  - apply: filterI => //; apply: filter_bigI => g Dg.
    have : (@closure cptTop W)g by rewrite -inE; apply: DsubW.
    move=> /(_ [set h | (forall x, B x -> (split_ent E5) (g x, h x)) /\ (forall x, B x -> (split_ent E5) (h x, g x))]).
    pull1. { apply: filterI; first exact: compact_cvg_nbhs.
      apply: (@compact_cvg_nbhs g B (((split_ent E5)^-1)%classic)) => //.
      exact: entourage_inv.
    }
    case=> g' [Wg' [P Q]]. 
    move/cvg_entourageP: (ctsW _ Wg' x) => /( _ (split_ent (split_ent E4))).
    pull1; first by []. 
    near_simpl=> G'; near=> y=> By.
    (do 2 apply: entourage_split => //).
    + by apply P; apply: nbhs_singleton.
    + exact: (near G' y).
    + exact: Q. 
    + exact: entourage_refl.
  - move=> f y Wf Uy; case: (Dcovers f); first exact: subset_closure.
    rewrite /R/R1 => f0 f0D [_ /interior_subset /= E4f].
    apply: (entourage_split (f0 y)) => //; last by 
      apply E3subE2, E4subE3, E4f, Uy.
    apply: (entourage_split (f0 x)) => //; first by 
      apply E4invsubE3, E4f, nbhs_singleton.
    apply E4subE3; by case: Uy=> [/(_ _ f0D) /= ].
Grab Existential Variables. end_near. Qed.

Lemma compact_pointwisePrecompact (W : set(X -> Y)): 
  @compact [topologicalType of {family compact, X -> Y}] W -> 
  pointwisePrecomact W.
Proof.
  move=> cptFamW x.
  have: @compact [topologicalType of {ptws X -> Y}] W. {
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

Lemma arzela_ascoli (W : (set ({family compact, X -> Y}))) : 
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
  + exact: compact_equicontinuous.
  + apply: (@pointwisePrecomact_subset _ (@closure
      [topologicalType of {family compact, X -> Y}] W)). 
    - by rewrite closure_limit_point => ??; left.
    - exact: compact_pointwisePrecompact.
Qed.

End Arzela.
    
