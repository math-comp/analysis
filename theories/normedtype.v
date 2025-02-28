(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum finmap matrix.
From mathcomp Require Import rat interval zmodp vector fieldext falgebra.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import archimedean.
From mathcomp Require Import cardinality set_interval ereal reals.
From mathcomp Require Import interval_inference topology prodnormedzmodule.
From mathcomp Require Import function_spaces.
From mathcomp Require Export real_interval separation_axioms tvs.

(**md**************************************************************************)
(* # Norm-related Notions                                                     *)
(*                                                                            *)
(* This file extends the topological hierarchy with norm-related notions.     *)
(* Note that balls in topology.v are not necessarily open, here they are.     *)
(* We used these definitions to prove the intermediate value theorem and      *)
(* the Heine-Borel theorem, which states that the compact sets of             *)
(* $\mathbb{R}^n$ are the closed and bounded sets, Urysohn's lemma, Vitali's  *)
(* covering lemmas (finite case and infinite case), etc.                      *)
(*                                                                            *)
(* We endow `numFieldType` with the types of norm-related notions (accessible *)
(* with `Import numFieldNormedType.Exports).                                  *)
(*                                                                            *)
(* * Limit superior and inferior:                                             *)
(*   limf_esup f F, limf_einf f F == limit sup/inferior of f at "filter" F    *)
(*                                   f has type X -> \bar R.                  *)
(*                                   F has type set (set X).                  *)
(*                                                                            *)
(* ## Normed topological abelian groups                                       *)
(* ```                                                                        *)
(*  pseudoMetricNormedZmodType R  == interface type for a normed topological  *)
(*                                   Abelian group equipped with a norm       *)
(*                                   The HB class is PseudoMetricNormedZmod.  *)
(* ```                                                                        *)
(*                                                                            *)
(* ```                                                                        *)
(*         lower_semicontinuous f == the extented real-valued function f is   *)
(*                                   lower-semicontinuous. The type of f is   *)
(*                                   X -> \bar R with X : topologicalType and *)
(*                                   R : realType                             *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Normed modules                                                          *)
(* ```                                                                        *)
(*                normedModType K == interface type for a normed module       *)
(*                                   structure over the numDomainType K       *)
(*                                   The HB class is NormedModule.            *)
(*                           `|x| == the norm of x (notation from ssrnum)     *)
(*                      ball_norm == balls defined by the norm.               *)
(*                          edist == the extended distance function for a     *)
(*                                   pseudometric X, from X * X -> \bar R     *)
(*                    edist_inf A == the infimum of distances to the set A    *)
(*                    Urysohn A B == a continuous function T -> [0,1] which   *)
(*                                   separates A and B when                   *)
(*                                   `uniform_separator A B`                  *)
(*       completely_regular_space == a space where points and closed sets can *)
(*                                   be separated by a function into R        *)
(*  completely_regular_uniformity == equips a completely_regular_space with   *)
(*                                   the uniformity induced by continuous     *)
(*                                   functions into the reals                 *)
(*                                   note this uniformity is always the only  *)
(*                                   choice, so its placed in a module        *)
(*          uniform_separator A B == there is a suitable uniform space and    *)
(*                                   entourage separating A and B             *)
(*                      nbhs_norm == neighborhoods defined by the norm        *)
(*                    closed_ball == closure of a ball                        *)
(*   f @`[ a , b ], f @`] a , b [ == notations for images of intervals,       *)
(*                                   intended for continuous, monotonous      *)
(*                                   functions, defined in ring_scope and     *)
(*                                   classical_set_scope respectively as:     *)
(*                  f @`[ a , b ] := `[minr (f a) (f b), maxr (f a) (f b)]%O  *)
(*                  f @`] a , b [ := `]minr (f a) (f b), maxr (f a) (f b)[%O  *)
(*                  f @`[ a , b ] := `[minr (f a) (f b),                      *)
(*                                     maxr (f a) (f b)]%classic              *)
(*                  f @`] a , b [ := `]minr (f a) (f b),                      *)
(*                                     maxr (f a) (f b)[%classic              *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Domination notations                                                    *)
(* ```                                                                        *)
(*              dominated_by h k f F == `|f| <= k * `|h|, near F              *)
(*                  bounded_near f F == f is bounded near F                   *)
(*            [bounded f x | x in A] == f is bounded on A, ie F := globally A *)
(*   [locally [bounded f x | x in A] == f is locally bounded on A             *)
(*                       bounded_set == set of bounded sets                   *)
(*                                   := [set A | [bounded x | x in A]]        *)
(*                       bounded_fun == set of functions bounded on their     *)
(*                                      whole domain                          *)
(*                                   := [set f | [bounded f x | x in setT]]   *)
(*                  lipschitz_on f F == f is lipschitz near F                 *)
(*          [lipschitz f x | x in A] == f is lipschitz on A                   *)
(* [locally [lipschitz f x | x in A] == f is locally lipschitz on A           *)
(*               k.-lipschitz_on f F == f is k.-lipschitz near F              *)
(*                  k.-lipschitz_A f == f is k.-lipschitz on A                *)
(*        [locally k.-lipschitz_A f] == f is locally k.-lipschitz on A        *)
(*                   contraction q f == f is q.-lipschitz and q < 1           *)
(*                  is_contraction f == exists q, f is q.-lipschitz and q < 1 *)
(*                                                                            *)
(*                     is_interval E == the set E is an interval              *)
(*                bigcup_ointsub U q == union of open real interval included  *)
(*                                      in U and that contain the rational    *)
(*                                      number q                              *)
(*                           Rhull A == the real interval hull of a set A     *)
(*                         shift x y == y + x                                 *)
(*                          center c := shift (- c)                           *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Complete normed modules                                                 *)
(* ```                                                                        *)
(*        completeNormedModType K == interface type for a complete normed     *)
(*                                   module structure over a realFieldType    *)
(*                                   K                                        *)
(*                                   The HB class is CompleteNormedModule.    *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Filters                                                                 *)
(* ```                                                                        *)
(*                     x^'-, x^'+ == filters on real numbers for predicates   *)
(*                                   s.t. nbhs holds on the left/right of x   *)
(* ```                                                                        *)
(*                                                                            *)
(* ```                                                                        *)
(*        cpoint A == the center of the set A if it is an open ball           *)
(*        radius A == the radius of the set A if it is an open ball           *)
(*                    Radius A has type {nonneg R} with R a numDomainType.    *)
(*       is_ball A == boolean predicate that holds when A is an open ball     *)
(*          k *` A == open ball with center cpoint A and radius k * radius A  *)
(*                    if A is an open ball and set0 o.w.                      *)
(*   vitali_collection_partition B V r n == subset of indices of V such the   *)
(*                    the ball B i has a radius between r/2^n+1 and r/2^n     *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "f @`[ a , b ]" (at level 20, b at level 9,
  format "f  @`[ a ,  b ]").
Reserved Notation "f @`] a , b [" (at level 20, b at level 9,
  format "f  @`] a ,  b [").
Reserved Notation "x ^'+" (at level 3, format "x ^'+").
Reserved Notation "x ^'-" (at level 3, format "x ^'-").
Reserved Notation "+oo_ R" (at level 3, format "+oo_ R").
Reserved Notation "-oo_ R" (at level 3, format "-oo_ R").
Reserved Notation "[ 'bounded' E | x 'in' A ]"
  (at level 0, x name, format "[ 'bounded'  E  |  x  'in'  A ]").
Reserved Notation "k .-lipschitz_on f"
  (at level 2, format "k .-lipschitz_on  f").
Reserved Notation "k .-lipschitz_ A f"
  (at level 2, A at level 0, format "k .-lipschitz_ A  f").
Reserved Notation "k .-lipschitz f" (at level 2, format "k .-lipschitz  f").
Reserved Notation "[ 'lipschitz' E | x 'in' A ]"
  (at level 0, x name, format "[ 'lipschitz'  E  |  x  'in'  A ]").
Reserved Notation "k *` A" (at level 40, left associativity, format "k  *`  A").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.
From mathcomp Require Import mathcomp_extra.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section limf_esup_einf.
Variables (T : choiceType) (X : filteredType T) (R : realFieldType).
Implicit Types (f : X -> \bar R) (F : set (set X)).
Local Open Scope ereal_scope.

Definition limf_esup f F := ereal_inf [set ereal_sup (f @` V) | V in F].

Definition limf_einf f F := - limf_esup (\- f) F.

Lemma limf_esupE f F :
  limf_esup f F = ereal_inf [set ereal_sup (f @` V) | V in F].
Proof. by []. Qed.

Lemma limf_einfE f F :
  limf_einf f F = ereal_sup [set ereal_inf (f @` V) | V in F].
Proof.
rewrite /limf_einf limf_esupE /ereal_inf oppeK -[in RHS]image_comp /=.
congr (ereal_sup [set _ | _ in [set ereal_sup _ | _ in _]]).
by under eq_fun do rewrite -image_comp.
Qed.

Lemma limf_esupN f F : limf_esup (\- f) F = - limf_einf f F.
Proof. by rewrite /limf_einf oppeK. Qed.

Lemma limf_einfN f F : limf_einf (\- f) F = - limf_esup f F.
Proof. by rewrite /limf_einf; under eq_fun do rewrite oppeK. Qed.

End limf_esup_einf.

Section limf_esup_einf_realType.
Variables (T : choiceType) (X : filteredType T) (R : realType).
Implicit Types (f : X -> \bar R) (F : set (set X)).
Local Open Scope ereal_scope.

Lemma limf_esup_ge0 f F : ~ F set0 ->
  (forall x, 0 <= f x) -> 0 <= limf_esup f F.
Proof.
move=> F0 f0; rewrite limf_esupE; apply: lb_ereal_inf => /= x [A].
have [-> /F0//|/set0P[y Ay FA] <-{x}] := eqVneq A set0.
by apply: ereal_sup_le; exists (f y).
Qed.

End limf_esup_einf_realType.

Lemma nbhsN (R : numFieldType) (x : R) : nbhs (- x) = -%R @ x.
Proof.
rewrite predeqE => A; split=> //= -[] e e_gt0 xeA; exists e => //= y /=.
  by move=> ?; apply: xeA => //=; rewrite -opprD normrN.
by rewrite -opprD normrN => ?; rewrite -[y]opprK; apply: xeA; rewrite /= opprK.
Qed.

Lemma cvg_compNP {T : topologicalType} {R : numFieldType} (f : R -> T) (a : R)
    (l : T) :
  (f \o -%R) x @[x --> a] --> l <-> f x @[x --> (- a)] --> l.
Proof. by rewrite nbhsN. Qed.

Lemma nbhsNimage (R : numFieldType) (x : R) :
  nbhs (- x) = [set -%R @` A | A in nbhs x].
Proof.
rewrite nbhsN /fmap/=; under eq_set => A do rewrite preimageEinv//= inv_oppr.
by rewrite (eq_imageK opprK opprK).
Qed.

Lemma nearN (R : numFieldType) (x : R) (P : R -> Prop) :
  (\forall y \near - x, P y) <-> \near x, P (- x).
Proof. by rewrite -near_simpl nbhsN. Qed.

Lemma openN (R : numFieldType) (A : set R) :
  open A -> open [set - x | x in A].
Proof.
move=> Aop; rewrite openE => _ [x /Aop x_A <-].
by rewrite /interior nbhsNimage; exists A.
Qed.

Lemma closedN (R : numFieldType) (A : set R) :
  closed A -> closed [set - x | x in A].
Proof.
move=> Acl x clNAx.
suff /Acl : closure A (- x) by exists (- x)=> //; rewrite opprK.
move=> B oppx_B; have : [set - x | x in A] `&` [set - x | x in B] !=set0.
  by apply: clNAx; rewrite -[x]opprK nbhsNimage; exists B.
move=> [y [[z Az oppzey] [t Bt opptey]]]; exists (- y).
by split; [rewrite -oppzey opprK|rewrite -opptey opprK].
Qed.

Lemma dnbhsN {R : numFieldType} (r : R) :
  (- r)%R^' = (fun A => -%R @` A) @` r^'.
Proof.
apply/seteqP; split=> [A [e/= e0 reA]|_/= [A [e/= e0 reA <-]]].
  exists (-%R @` A).
    exists e => // x/= rxe xr; exists (- x)%R; rewrite ?opprK//.
    by apply: reA; rewrite ?eqr_opp//= opprK addrC distrC.
  rewrite image_comp (_ : _ \o _ = idfun) ?image_id// funeqE => x/=.
  by rewrite opprK.
exists e => //= x/=; rewrite -opprD normrN => axe xa.
exists (- x)%R; rewrite ?opprK//; apply: reA; rewrite ?eqr_oppLR//=.
by rewrite opprK.
Qed.

HB.mixin Record NormedZmod_PseudoMetric_eq (R : numDomainType) T
    of Num.NormedZmodule R T & PseudoPointedMetric R T := {
  pseudo_metric_ball_norm : ball = ball_ (fun x : T => `| x |)
}.

#[short(type="pseudoMetricNormedZmodType")]
HB.structure Definition PseudoMetricNormedZmod (R : numDomainType) :=
  {T of Num.NormedZmodule R T & PseudoMetric R T
   & NormedZmod_PseudoMetric_eq R T & isPointed T}.

Section pseudoMetricnormedzmodule_lemmas.
Context {K : numDomainType} {V : pseudoMetricNormedZmodType K}.

Local Notation ball_norm := (ball_ (@normr K V)).

Lemma ball_normE : ball_norm = ball.
Proof. by rewrite pseudo_metric_ball_norm. Qed.

End pseudoMetricnormedzmodule_lemmas.

Lemma bigcup_ballT {R : realType} : \bigcup_n ball (0%R : R) n%:R = setT.
Proof.
apply/seteqP; split => // x _; have [x0|x0] := ltP 0%R x.
  exists `|ceil x|.+1 => //.
  rewrite /ball /= sub0r normrN gtr0_norm// (le_lt_trans (ceil_ge _))//.
  by rewrite -natr1 natr_absz -abszE gtz0_abs// -?ceil_gt0// ltr_pwDr.
exists `|ceil (- x)|.+1 => //.
rewrite /ball /= sub0r normrN ler0_norm// (le_lt_trans (ceil_ge _))//.
rewrite -natr1 natr_absz -abszE gez0_abs ?ltr_pwDr// -ceil_ge0 ltrNl opprK.
by rewrite (le_lt_trans x0).
Qed.

Section lower_semicontinuous.
Context {X : topologicalType} {R : realType}.
Implicit Types f : X -> \bar R.
Local Open Scope ereal_scope.

Definition lower_semicontinuous f := forall x a, a%:E < f x ->
  exists2 V, nbhs x V & forall y, V y -> a%:E < f y.

Lemma lower_semicontinuousP f :
  lower_semicontinuous f <-> forall a, open [set x | f x > a%:E].
Proof.
split=> [sci a|openf x a afx].
  rewrite openE /= => x /= /sci[A + Aaf]; rewrite nbhsE /= => -[B xB BA].
  apply: nbhs_singleton; apply: nbhs_interior.
  by rewrite nbhsE /=; exists B => // y /BA /=; exact: Aaf.
exists [set x | a%:E < f x] => //.
by rewrite nbhsE/=; exists [set x | a%:E < f x].
Qed.

End lower_semicontinuous.

(** neighborhoods *)

Section Nbhs'.
Context {R : numDomainType} {T : pseudoMetricType R}.

Lemma ex_ball_sig (x : T) (P : set T) :
  ~ (forall eps : {posnum R}, ~ (ball x eps%:num `<=` ~` P)) ->
    {d : {posnum R} | ball x d%:num `<=` ~` P}.
Proof.
rewrite forallNE notK => exNP.
pose D := [set d : R^o | d > 0 /\ ball x d `<=` ~` P].
have [|d_gt0] := @getPex _ D; last by exists (PosNum d_gt0).
by move: exNP => [e eP]; exists e%:num.
Qed.

Lemma nbhsC (x : T) (P : set T) :
  ~ (forall eps : {posnum R}, ~ (ball x eps%:num `<=` ~` P)) ->
  nbhs x (~` P).
Proof. by move=> /ex_ball_sig [e] ?; apply/nbhs_ballP; exists e%:num => /=. Qed.

Lemma nbhsC_ball (x : T) (P : set T) :
  nbhs x (~` P) -> {d : {posnum R} | ball x d%:num `<=` ~` P}.
Proof.
move=> /nbhs_ballP xNP; apply: ex_ball_sig.
by have [_ /posnumP[e] eP /(_ _ eP)] := xNP.
Qed.

Lemma nbhs_ex (x : T) (P : T -> Prop) : nbhs x P ->
  {d : {posnum R} | forall y, ball x d%:num y -> P y}.
Proof.
move=> /nbhs_ballP xP.
pose D := [set d : R^o | d > 0 /\ forall y, ball x d y -> P y].
have [|d_gt0 dP] := @getPex _ D; last by exists (PosNum d_gt0).
by move: xP => [e bP]; exists (e : R).
Qed.

End Nbhs'.

Lemma coord_continuous {K : numFieldType} m n i j :
  continuous (fun M : 'M[K]_(m, n) => M i j).
Proof.
move=> /= M s /= /(nbhs_ballP (M i j)) [e e0 es].
apply/nbhs_ballP; exists e => //= N MN; exact/es/MN.
Qed.

Global Instance Proper_dnbhs_numFieldType (R : numFieldType) (x : R) :
  ProperFilter x^'.
Proof.
apply: Build_ProperFilter_ex => A /nbhs_ballP[_/posnumP[e] Ae].
exists (x + e%:num / 2); apply: Ae; last first.
  by rewrite eq_sym addrC -subr_eq subrr eq_sym.
rewrite /ball /= opprD addrCA addKr normrN ger0_norm //.
by rewrite {2}(splitr e%:num) ltr_pwDl.
Qed.

#[global] Hint Extern 0 (ProperFilter _^') =>
  (apply: Proper_dnbhs_numFieldType) : typeclass_instances.

(** Some Topology on extended real numbers *)

Definition pinfty_nbhs (R : numFieldType) : set_system R :=
  fun P => exists M, M \is Num.real /\ forall x, M < x -> P x.
Arguments pinfty_nbhs R : clear implicits.
Definition ninfty_nbhs (R : numFieldType) : set_system R :=
  fun P => exists M, M \is Num.real /\ forall x, x < M -> P x.
Arguments ninfty_nbhs R : clear implicits.

Notation "+oo_ R" := (pinfty_nbhs R)
  (only parsing) : ring_scope.
Notation "-oo_ R" := (ninfty_nbhs R)
  (only parsing) : ring_scope.

Notation "+oo" := (pinfty_nbhs _) : ring_scope.
Notation "-oo" := (ninfty_nbhs _) : ring_scope.

Lemma ninftyN {R : numFieldType} : (- x : R)%R @[x --> -oo] = +oo.
Proof.
apply/seteqP; split => [A [M [Mreal MA]]|A [M [Mreal MA]]].
  exists (- M); rewrite realN; split => // x.
  by rewrite ltrNl => /MA/=; rewrite opprK.
by exists (- M); rewrite ?realN; split=> // x; rewrite ltrNr => /MA.
Qed.

Lemma ninfty {R : numFieldType} : (- x : R)%R @[x --> +oo] = -oo.
Proof.
apply/seteqP; split => [A [M [Mreal MA]]|A [M [Mreal MA]]].
  exists (- M); rewrite realN; split => // x.
  by rewrite -ltrNr => /MA/=; rewrite opprK.
by exists (- M); rewrite ?realN; split=> // x; rewrite ltrNl => /MA.
Qed.

Section infty_nbhs_instances.
Context {R : numFieldType}.
Implicit Types r : R.

Global Instance proper_pinfty_nbhs : ProperFilter (pinfty_nbhs R).
Proof.
apply Build_ProperFilter_ex.
  by move=> P [M [Mreal MP]]; exists (M + 1); apply MP; rewrite ltrDl.
split=> /= [|P Q [MP [MPr gtMP]] [MQ [MQr gtMQ]] |P Q sPQ [M [Mr gtM]]].
- by exists 0.
- exists (maxr MP MQ); split=> [|x]; first exact: max_real.
  by rewrite comparable_gt_max ?real_comparable // => /andP[/gtMP ? /gtMQ].
- by exists M; split => // ? /gtM /sPQ.
Qed.

Global Instance proper_ninfty_nbhs : ProperFilter (ninfty_nbhs R).
Proof.
apply Build_ProperFilter_ex.
  move=> P [M [Mr ltMP]]; exists (M - 1).
  by apply: ltMP; rewrite gtrDl oppr_lt0.
split=> /= [|P Q [MP [MPr ltMP]] [MQ [MQr ltMQ]] |P Q sPQ [M [Mr ltM]]].
- by exists 0.
- exists (Num.min MP MQ); split=> [|x]; first exact: min_real.
  by rewrite comparable_lt_min ?real_comparable // => /andP[/ltMP ? /ltMQ].
- by exists M; split => // x /ltM /sPQ.
Qed.

Lemma nbhs_pinfty_gt r : r \is Num.real -> \forall x \near +oo, r < x.
Proof. by exists r. Qed.

Lemma nbhs_pinfty_ge r : r \is Num.real -> \forall x \near +oo, r <= x.
Proof. by exists r; split => //; apply: ltW. Qed.

Lemma nbhs_ninfty_lt r : r \is Num.real -> \forall x \near -oo, r > x.
Proof. by exists r. Qed.

Lemma nbhs_ninfty_le r : r \is Num.real -> \forall x \near -oo, r >= x.
Proof. by exists r; split => // ?; apply: ltW. Qed.

Lemma nbhs_pinfty_real : \forall x \near +oo, x \is @Num.real R.
Proof. by apply: filterS (nbhs_pinfty_gt (@real0 _)); apply: gtr0_real. Qed.

Lemma nbhs_ninfty_real : \forall x \near -oo, x \is @Num.real R.
Proof. by apply: filterS (nbhs_ninfty_lt (@real0 _)); apply: ltr0_real. Qed.

Lemma pinfty_ex_gt (m : R) (A : set R) : m \is Num.real ->
  (\forall k \near +oo, A k) -> exists2 M, m < M & A M.
Proof.
move=> m_real Agt; near (pinfty_nbhs R) => M.
by exists M; near: M => //; apply: nbhs_pinfty_gt.
Unshelve. all: by end_near. Qed.

Lemma pinfty_ex_ge (m : R) (A : set R) : m \is Num.real ->
  (\forall k \near +oo, A k) -> exists2 M, m <= M & A M.
Proof.
move=> m_real Agt; near (pinfty_nbhs R) => M.
by exists M; near: M => //; apply: nbhs_pinfty_ge.
Unshelve. all: by end_near. Qed.

Lemma pinfty_ex_gt0 (A : set R) :
  (\forall k \near +oo, A k) -> exists2 M, M > 0 & A M.
Proof. exact: pinfty_ex_gt. Qed.

Lemma near_pinfty_div2 (A : set R) :
  (\forall k \near +oo, A k) -> (\forall k \near +oo, A (k / 2)).
Proof.
move=> [M [Mreal AM]]; exists (M * 2); split; first by rewrite realM.
by move=> x; rewrite -ltr_pdivlMr //; exact: AM.
Qed.

Lemma not_near_inftyP (P : pred R) :
  ~ (\forall x \near +oo, P x) <->
    forall M : R, M \is Num.real -> exists2 x, M < x & ~ P x.
Proof.
rewrite nearE -forallNP -propeqE; apply: eq_forall => M.
by rewrite propeqE -implypN existsPNP.
Qed.

Lemma not_near_ninftyP (P : pred R):
  ~ (\forall x \near -oo, P x) <->
    forall M : R, M \is Num.real -> exists2 x, x < M & ~ P x.
Proof.
rewrite -filterN ninftyN not_near_inftyP/=; split => PN M; rewrite -realN;
by move=> /PN[x Mx PNx]; exists (- x) => //; rewrite 1?(ltrNl,ltrNr,opprK).
Qed.

End infty_nbhs_instances.

#[global] Hint Extern 0 (is_true (_ < ?x)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_pinfty_gt end : core.
#[global] Hint Extern 0 (is_true (_ <= ?x)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_pinfty_ge end : core.
#[global] Hint Extern 0 (is_true (_ > ?x)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_ninfty_lt end : core.
#[global] Hint Extern 0 (is_true (_ >= ?x)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_ninfty_le end : core.
#[global] Hint Extern 0 (is_true (?x \is Num.real)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_pinfty_real end : core.
#[global] Hint Extern 0 (is_true (?x \is Num.real)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_ninfty_real end : core.

#[global] Hint Extern 0 (is_true (_ < ?x)%E) => match goal with
  H : x \is_near _ |- _ => near: x; exact: ereal_nbhs_pinfty_gt end : core.
#[global] Hint Extern 0 (is_true (_ <= ?x)%E) => match goal with
  H : x \is_near _ |- _ => near: x; exact: ereal_nbhs_pinfty_ge end : core.
#[global] Hint Extern 0 (is_true (_ > ?x)%E) => match goal with
  H : x \is_near _ |- _ => near: x; exact: ereal_nbhs_ninfty_lt end : core.
#[global] Hint Extern 0 (is_true (_ >= ?x)%E) => match goal with
  H : x \is_near _ |- _ => near: x; exact: ereal_nbhs_ninfty_le end : core.
#[global] Hint Extern 0 (is_true (fine ?x \is Num.real)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: ereal_nbhs_pinfty_real end : core.
#[global] Hint Extern 0 (is_true (fine ?x \is Num.real)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: ereal_nbhs_ninfty_real end : core.

Section cvg_infty_numField.
Context {R : numFieldType}.

Let cvgryPnum {F : set_system R} {FF : Filter F} : [<->
(* 0 *) F --> +oo;
(* 1 *) forall A, A \is Num.real -> \forall x \near F, A <= x;
(* 2 *) forall A, A \is Num.real -> \forall x \near F, A < x;
(* 3 *) \forall A \near +oo, \forall x \near F, A < x;
(* 4 *) \forall A \near +oo, \forall x \near F, A <= x ].
Proof.
tfae; first by move=> Foo A Areal; apply: Foo; apply: nbhs_pinfty_ge.
- move=> AF A Areal; near +oo_R => B.
  by near do apply: (@lt_le_trans _ _ B) => //=; apply: AF.
- by move=> Foo; near do apply: Foo => //.
- by apply: filterS => ?; apply: filterS => ?; apply: ltW.
case=> [A [AR AF]] P [x [xR Px]]; near +oo_R => B.
by near do [apply: Px; apply: (@lt_le_trans _ _ B) => //]; apply: AF.
Unshelve. all: by end_near. Qed.

Let cvgrNyPnum {F : set_system R} {FF : Filter F} : [<->
(* 0 *) F --> -oo;
(* 1 *) forall A, A \is Num.real -> \forall x \near F, A >= x;
(* 2 *) forall A, A \is Num.real -> \forall x \near F, A > x;
(* 3 *) \forall A \near -oo, \forall x \near F, A > x;
(* 4 *) \forall A \near -oo, \forall x \near F, A >= x ].
Proof.
tfae; first by move=> Foo A Areal; apply: Foo; apply: nbhs_ninfty_le.
- move=> AF A Areal; near -oo_R => B.
  by near do apply: (@le_lt_trans _ _ B) => //; apply: AF.
- by move=> Foo; near do apply: Foo => //.
- by apply: filterS => ?; apply: filterS => ?; apply: ltW.
case=> [A [AR AF]] P [x [xR Px]]; near -oo_R => B.
by near do [apply: Px; apply: (@le_lt_trans _ _ B) => //]; apply: AF.
Unshelve. all: end_near. Qed.

Context {T} {F : set_system T} {FF : Filter F}.
Implicit Types f : T -> R.

Lemma cvgryPger f :
  f @ F --> +oo <-> forall A, A \is Num.real -> \forall x \near F, A <= f x.
Proof. exact: (cvgryPnum 0%N 1%N). Qed.

Lemma cvgryPgtr f :
  f @ F --> +oo <-> forall A, A \is Num.real -> \forall x \near F, A < f x.
Proof. exact: (cvgryPnum 0%N 2%N). Qed.

Lemma cvgryPgty f :
  f @ F --> +oo <-> \forall A \near +oo, \forall x \near F, A < f x.
Proof. exact: (cvgryPnum 0%N 3%N). Qed.

Lemma cvgryPgey f :
  f @ F --> +oo <-> \forall A \near +oo, \forall x \near F, A <= f x.
Proof. exact: (cvgryPnum 0%N 4%N). Qed.

Lemma cvgrNyPler f :
  f @ F --> -oo <-> forall A, A \is Num.real -> \forall x \near F, A >= f x.
Proof. exact: (cvgrNyPnum 0%N 1%N). Qed.

Lemma cvgrNyPltr f :
  f @ F --> -oo <-> forall A, A \is Num.real -> \forall x \near F, A > f x.
Proof. exact: (cvgrNyPnum 0%N 2%N). Qed.

Lemma cvgrNyPltNy f :
  f @ F --> -oo <-> \forall A \near -oo, \forall x \near F, A > f x.
Proof. exact: (cvgrNyPnum 0%N 3%N). Qed.

Lemma cvgrNyPleNy f :
  f @ F --> -oo <-> \forall A \near -oo, \forall x \near F, A >= f x.
Proof. exact: (cvgrNyPnum 0%N 4%N). Qed.

Lemma cvgry_ger f :
  f @ F --> +oo -> forall A, A \is Num.real -> \forall x \near F, A <= f x.
Proof. by rewrite cvgryPger. Qed.

Lemma cvgry_gtr f :
  f @ F --> +oo -> forall A, A \is Num.real -> \forall x \near F, A < f x.
Proof. by rewrite cvgryPgtr. Qed.

Lemma cvgrNy_ler f :
  f @ F --> -oo -> forall A, A \is Num.real -> \forall x \near F, A >= f x.
Proof. by rewrite cvgrNyPler. Qed.

Lemma cvgrNy_ltr f :
  f @ F --> -oo -> forall A, A \is Num.real -> \forall x \near F, A > f x.
Proof. by rewrite cvgrNyPltr. Qed.

Lemma cvgNry f : (- f @ F --> +oo) <-> (f @ F --> -oo).
Proof.
rewrite cvgrNyPler cvgryPger; split=> Foo A Areal;
by near do rewrite -lerN2 ?opprK; apply: Foo; rewrite rpredN.
Unshelve. all: end_near. Qed.

Lemma cvgNrNy f : (- f @ F --> -oo) <-> (f @ F --> +oo).
Proof. by rewrite -cvgNry opprK. Qed.

End cvg_infty_numField.

Section cvg_infty_realField.
Context {R : realFieldType}.
Context {T} {F : set_system T} {FF : Filter F} (f : T -> R).

Lemma cvgryPge : f @ F --> +oo <-> forall A, \forall x \near F, A <= f x.
Proof.
by rewrite cvgryPger; under eq_forall do rewrite num_real; split=> + *; apply.
Qed.

Lemma cvgryPgt : f @ F --> +oo <-> forall A, \forall x \near F, A < f x.
Proof.
by rewrite cvgryPgtr; under eq_forall do rewrite num_real; split=> + *; apply.
Qed.

Lemma cvgrNyPle : f @ F --> -oo <-> forall A, \forall x \near F, A >= f x.
Proof.
by rewrite cvgrNyPler; under eq_forall do rewrite num_real; split=> + *; apply.
Qed.

Lemma cvgrNyPlt : f @ F --> -oo <-> forall A, \forall x \near F, A > f x.
Proof.
by rewrite cvgrNyPltr; under eq_forall do rewrite num_real; split=> + *; apply.
Qed.

Lemma cvgry_ge : f @ F --> +oo -> forall A, \forall x \near F, A <= f x.
Proof. by rewrite cvgryPge. Qed.

Lemma cvgry_gt : f @ F --> +oo -> forall A, \forall x \near F, A < f x.
Proof. by rewrite cvgryPgt. Qed.

Lemma cvgrNy_le : f @ F --> -oo -> forall A, \forall x \near F, A >= f x.
Proof. by rewrite cvgrNyPle. Qed.

Lemma cvgrNy_lt : f @ F --> -oo -> forall A, \forall x \near F, A > f x.
Proof. by rewrite cvgrNyPlt. Qed.

End cvg_infty_realField.

Lemma cvgrnyP {R : realType} {T} {F : set_system T} {FF : Filter F} (f : T -> nat) :
   (((f n)%:R : R) @[n --> F] --> +oo) <-> (f @ F --> \oo).
Proof.
split=> [/cvgryPge|/cvgnyPge] Foo.
  by apply/cvgnyPge => A; near do rewrite -(@ler_nat R); apply: Foo.
apply/cvgryPgey; near=> A; near=> n.
rewrite pmulrn ceil_le_int// [ceil _]intEsign.
by rewrite le_gtF ?expr0 ?mul1r ?lez_nat -?ceil_ge0//; near: n; apply: Foo.
Unshelve. all: by end_near. Qed.

Section monotonic_itv_bigcup.
Context {R : realType}.
Implicit Types (F : R -> R) (a : R).

Lemma decreasing_itvNyo_bigcup F a :
  {in `[a, +oo[ &, {homo F : x y /~ x < y}} ->
  F x @[x --> +oo] --> -oo ->
  (`]-oo, F a[ = \bigcup_i `]F (a + i.+1%:R), F a[)%classic.
Proof.
move=> dF nyF; rewrite itvNy_bnd_bigcup_BLeft eqEsubset; split.
- move=> y/= [n _]/=; rewrite in_itv/= => /andP[Fany yFa].
  have [i iFan] : exists i, F (a + i.+1%:R) < F a - n%:R.
    move/cvgrNy_lt : nyF.
    move/(_ (F a - n%:R)) => [z [zreal zFan]].
    exists `|ceil (z - a)|%N.
    rewrite zFan// -ltrBlDl.
    rewrite (le_lt_trans (Num.Theory.le_ceil _))  ?num_real//.
    by rewrite (le_lt_trans (ler_norm _))// -natr1 -intr_norm ltrDl.
  by exists i => //=; rewrite in_itv/= yFa (lt_le_trans _ Fany).
- move=> z/= [n _ /=]; rewrite in_itv/= => /andP[Fanz zFa].
  exists `|ceil (F (a + n.+1%:R) - F a)%R|.+1 => //=.
  rewrite in_itv/= zFa andbT lerBlDr -lerBlDl (le_trans _ (abs_ceil_ge _))//.
  by rewrite ler_normr orbC opprB lerB// ltW.
Qed.

Lemma decreasing_itvoo_bigcup F a n :
  {in `[a, +oo[ &, {homo F : x y /~ x < y}} ->
  (`]F (a + n%:R), F a[ = \bigcup_(i < n) `]F (a + i.+1%:R), F a[)%classic.
Proof.
move=> decrF; rewrite eqEsubset; split.
- move: n => [|n]; first by rewrite addr0 set_itvoo0.
  by apply: (@bigcup_sup _ _ n) => /=.
- apply: bigcup_sub => k/= kn; apply: subset_itvr; rewrite bnd_simp.
  move: kn; rewrite leq_eqVlt => /predU1P[<-//|kn].
  by rewrite ltW// decrF ?in_itv/= ?andbT ?lerDl//= ltrD2l ltr_nat.
Qed.

Lemma increasing_itvNyo_bigcup F a :
  {in `]-oo, a] &, {homo F : x y / x < y}} ->
  F x @[x --> -oo] --> -oo ->
 (`]-oo, F a] = \bigcup_i `]F (a - i.+1%:R), F a])%classic.
Proof.
move=> dF nyF; rewrite itvNy_bnd_bigcup_BLeft eqEsubset; split.
- move=> y/= [n _]/=; rewrite in_itv/= => /andP[Fany yFa].
  have [i iFan] : exists i, F (a - i.+1%:R) < F a - n%:R.
    move/cvgrNy_lt : nyF.
    move/(_ (F a - n%:R)) => [z [zreal zFan]].
    exists `|ceil (a - z)|%N.
    rewrite zFan// ltrBlDr -ltrBlDl.
    rewrite (le_lt_trans (Num.Theory.le_ceil _)) ?num_real//.
    by rewrite (le_lt_trans (ler_norm _))// -natr1 -intr_norm ltrDl.
  by exists i => //=; rewrite in_itv/= yFa andbT (lt_le_trans _ Fany).
- move=> z/= [n _ /=]; rewrite in_itv/= => /andP[Fanz zFa].
  exists `| ceil (F (a - n.+1%:R) - F a)%R |.+1 => //=.
  rewrite in_itv/= zFa andbT lerBlDr -lerBlDl (le_trans _ (abs_ceil_ge _))//.
  by rewrite ler_normr orbC opprB lerB// ltW.
Qed.

Lemma increasing_itvoc_bigcup F a n :
  {in `]-oo, a] &, {homo F : x y / x < y}} ->
  (`]F (a - n%:R), F a] = \bigcup_(i < n) `]F (a - i.+1%:R), F a])%classic.
Proof.
move=> incrF; rewrite eqEsubset; split.
- move: n => [|n]; first by rewrite subr0 set_itvoc0.
  by apply: (@bigcup_sup _ _ n) => /=.
- apply: bigcup_sub => k/= kn; apply: subset_itvr; rewrite bnd_simp.
  move: kn; rewrite leq_eqVlt => /predU1P[<-//|kn].
  by rewrite ltW// incrF ?in_itv/= ?andbT ?gerBl ?ler_ltB ?ltr_nat.
Qed.

End monotonic_itv_bigcup.

Section ecvg_infty_numField.
Local Open Scope ereal_scope.

Context {R : numFieldType}.

Let cvgeyPnum {F : set_system \bar R} {FF : Filter F} : [<->
(* 0 *) F --> +oo;
(* 1 *) forall A, A \is Num.real -> \forall x \near F, A%:E <= x;
(* 2 *) forall A, A \is Num.real -> \forall x \near F, A%:E < x;
(* 3 *) \forall A \near +oo%R, \forall x \near F, A%:E < x;
(* 4 *) \forall A \near +oo%R, \forall x \near F, A%:E <= x ].
Proof.
tfae; first by move=> Foo A Areal; apply: Foo; apply: ereal_nbhs_pinfty_ge.
- move=> AF A Areal; near +oo_R => B.
  by near do rewrite (@lt_le_trans _ _ B%:E) ?lte_fin//; apply: AF.
- by move=> Foo; near do apply: Foo => //.
- by apply: filterS => ?; apply: filterS => ?; apply: ltW.
case=> [A [AR AF]] P [x [xR Px]]; near +oo_R => B.
by near do [apply: Px; rewrite (@lt_le_trans _ _ B%:E) ?lte_fin//]; apply: AF.
Unshelve. all: end_near. Qed.

Let cvgeNyPnum {F : set_system \bar R} {FF : Filter F} : [<->
(* 0 *) F --> -oo;
(* 1 *) forall A, A \is Num.real -> \forall x \near F, A%:E >= x;
(* 2 *) forall A, A \is Num.real -> \forall x \near F, A%:E > x;
(* 3 *) \forall A \near -oo%R, \forall x \near F, A%:E > x;
(* 4 *) \forall A \near -oo%R, \forall x \near F, A%:E >= x ].
Proof.
tfae; first by move=> Foo A Areal; apply: Foo; apply: ereal_nbhs_ninfty_le.
- move=> AF A Areal; near -oo_R => B.
  by near do rewrite (@le_lt_trans _ _ B%:E) ?lte_fin//; apply: AF.
- by move=> Foo; near do apply: Foo => //.
- by apply: filterS => ?; apply: filterS => ?; apply: ltW.
case=> [A [AR AF]] P [x [xR Px]]; near -oo_R => B.
by near do [apply: Px; rewrite (@le_lt_trans _ _ B%:E) ?lte_fin//]; apply: AF.
Unshelve. all: end_near. Qed.

Context {T} {F : set_system T} {FF : Filter F}.
Implicit Types (f : T -> \bar R) (u : T -> R).

Lemma cvgeyPger f :
  f @ F --> +oo <-> forall A, A \is Num.real -> \forall x \near F, A%:E <= f x.
Proof. exact: (cvgeyPnum 0%N 1%N). Qed.

Lemma cvgeyPgtr f :
  f @ F --> +oo <-> forall A, A \is Num.real -> \forall x \near F, A%:E < f x.
Proof. exact: (cvgeyPnum 0%N 2%N). Qed.

Lemma cvgeyPgty f :
  f @ F --> +oo <-> \forall A \near +oo%R, \forall x \near F, A%:E < f x.
Proof. exact: (cvgeyPnum 0%N 3%N). Qed.

Lemma cvgeyPgey f :
  f @ F --> +oo <-> \forall A \near +oo%R, \forall x \near F, A%:E <= f x.
Proof. exact: (cvgeyPnum 0%N 4%N). Qed.

Lemma cvgeNyPler f :
  f @ F --> -oo <-> forall A, A \is Num.real -> \forall x \near F, A%:E >= f x.
Proof. exact: (cvgeNyPnum 0%N 1%N). Qed.

Lemma cvgeNyPltr f :
  f @ F --> -oo <-> forall A, A \is Num.real -> \forall x \near F, A%:E > f x.
Proof. exact: (cvgeNyPnum 0%N 2%N). Qed.

Lemma cvgeNyPltNy f :
  f @ F --> -oo <-> \forall A \near -oo%R, \forall x \near F, A%:E > f x.
Proof. exact: (cvgeNyPnum 0%N 3%N). Qed.

Lemma cvgeNyPleNy f :
  f @ F --> -oo <-> \forall A \near -oo%R, \forall x \near F, A%:E >= f x.
Proof. exact: (cvgeNyPnum 0%N 4%N). Qed.

Lemma cvgey_ger f :
  f @ F --> +oo -> forall A, A \is Num.real -> \forall x \near F, A%:E <= f x.
Proof. by rewrite cvgeyPger. Qed.

Lemma cvgey_gtr f :
  f @ F --> +oo -> forall A, A \is Num.real -> \forall x \near F, A%:E < f x.
Proof. by rewrite cvgeyPgtr. Qed.

Lemma cvgeNy_ler f :
  f @ F --> -oo -> forall A, A \is Num.real -> \forall x \near F, A%:E >= f x.
Proof. by rewrite cvgeNyPler. Qed.

Lemma cvgeNy_ltr f :
  f @ F --> -oo -> forall A, A \is Num.real -> \forall x \near F, A%:E > f x.
Proof. by rewrite cvgeNyPltr. Qed.

Lemma cvgNey f : (\- f @ F --> +oo) <-> (f @ F --> -oo).
Proof.
rewrite cvgeNyPler cvgeyPger; split=> Foo A Areal;
by near do rewrite -leeN2 ?oppeK; apply: Foo; rewrite rpredN.
Unshelve. all: end_near. Qed.

Lemma cvgNeNy f : (\- f @ F --> -oo) <-> (f @ F --> +oo).
Proof.
by rewrite -cvgNey (_ : \- \- f = f)//; apply/funeqP => x /=; rewrite oppeK.
Qed.

Lemma cvgeryP u : ((u x)%:E @[x --> F] --> +oo) <-> (u @ F --> +oo%R).
Proof.
split=> [/cvgeyPger|/cvgryPger] Foo.
  by apply/cvgryPger => A Ar; near do rewrite -lee_fin; apply: Foo.
by apply/cvgeyPger => A Ar; near do rewrite lee_fin; apply: Foo.
Unshelve. all: end_near. Qed.

Lemma cvgerNyP u : ((u x)%:E @[x --> F] --> -oo) <-> (u @ F --> -oo%R).
Proof.
split=> [/cvgeNyPler|/cvgrNyPler] Foo.
  by apply/cvgrNyPler => A Ar; near do rewrite -lee_fin; apply: Foo.
by apply/cvgeNyPler => A Ar; near do rewrite lee_fin; apply: Foo.
Unshelve. all: end_near. Qed.

End ecvg_infty_numField.

Section ecvg_infty_realField.
Local Open Scope ereal_scope.
Context {R : realFieldType}.
Context {T} {F : set_system T} {FF : Filter F} (f : T -> \bar R).

Lemma cvgeyPge : f @ F --> +oo <-> forall A, \forall x \near F, A%:E <= f x.
Proof.
by rewrite cvgeyPger; under eq_forall do rewrite num_real; split=> + *; apply.
Qed.

Lemma cvgeyPgt : f @ F --> +oo <-> forall A, \forall x \near F, A%:E < f x.
Proof.
by rewrite cvgeyPgtr; under eq_forall do rewrite num_real; split=> + *; apply.
Qed.

Lemma cvgeNyPle : f @ F --> -oo <-> forall A, \forall x \near F, A%:E >= f x.
Proof.
by rewrite cvgeNyPler; under eq_forall do rewrite num_real; split=> + *; apply.
Qed.

Lemma cvgeNyPlt : f @ F --> -oo <-> forall A, \forall x \near F, A%:E > f x.
Proof.
by rewrite cvgeNyPltr; under eq_forall do rewrite num_real; split=> + *; apply.
Qed.

Lemma cvgey_ge : f @ F --> +oo -> forall A, \forall x \near F, A%:E <= f x.
Proof. by rewrite cvgeyPge. Qed.

Lemma cvgey_gt : f @ F --> +oo -> forall A, \forall x \near F, A%:E < f x.
Proof. by rewrite cvgeyPgt. Qed.

Lemma cvgeNy_le : f @ F --> -oo -> forall A, \forall x \near F, A%:E >= f x.
Proof. by rewrite cvgeNyPle. Qed.

Lemma cvgeNy_lt : f @ F --> -oo -> forall A, \forall x \near F, A%:E > f x.
Proof. by rewrite cvgeNyPlt. Qed.

End ecvg_infty_realField.

Lemma cvgenyP {R : realType} {T} {F : set_system T} {FF : Filter F} (f : T -> nat) :
   (((f n)%:R : R)%:E @[n --> F] --> +oo%E) <-> (f @ F --> \oo).
Proof. by rewrite cvgeryP cvgrnyP. Qed.

Lemma gt0_cvgMlNy {R : realFieldType} (M : R) (f : R -> R) : (0 < M)%R ->
  (f r) @[r --> -oo] --> -oo -> (f r * M)%R @[r --> -oo] --> -oo.
Proof.
move=> M0 /cvgrNyPle fy; apply/cvgrNyPle => A.
by apply: filterS (fy (A / M)) => x; rewrite ler_pdivlMr.
Qed.

Lemma gt0_cvgMly {R : realFieldType} (M : R) (f : R -> R) : (0 < M)%R ->
  f r @[r --> +oo] --> +oo -> (f r * M)%R @[r --> +oo] --> +oo.
Proof.
move=> M0 /cvgryPge fy; apply/cvgryPge => A.
apply: filterS (fy (A / M)) => x.
by rewrite ler_pdivrMr.
Qed.

(** Modules with a norm depending on a numDomain*)

HB.mixin Record PseudoMetricNormedZmod_Tvs_isNormedModule K V
    of PseudoMetricNormedZmod K V & Tvs K V := {
  normrZ : forall (l : K) (x : V), `| l *: x | = `| l | * `| x |;
}.

#[short(type="normedModType")]
HB.structure Definition NormedModule (K : numDomainType) :=
  {T of PseudoMetricNormedZmod K T & Tvs K T
   & PseudoMetricNormedZmod_Tvs_isNormedModule K T}.

HB.factory Record PseudoMetricNormedZmod_Lmodule_isNormedModule (K : numFieldType) V
    of PseudoMetricNormedZmod K V & GRing.Lmodule K V := {
 normrZ : forall (l : K) (x : V), `| l *: x | = `| l | * `| x |;
}.

HB.builders Context K V of PseudoMetricNormedZmod_Lmodule_isNormedModule K V.

(* NB: These lemmas are done later with more machinery. They should
   be simplified once normedtype is split, and the present section can
   depend on near lemmas on pseudometricnormedzmodtype ?*)
Lemma add_continuous : continuous (fun x : V * V => x.1 + x.2).
Proof.
move=> [/= x y]; apply/cvg_ballP => e e0 /=.
exists (ball x (e / 2), ball y (e / 2)) => /=.
  by split; apply: nbhsx_ballx; rewrite divr_gt0.
rewrite -ball_normE /ball_/= => xy /= [nx ny].
by rewrite opprD addrACA (le_lt_trans (ler_normD _ _)) // (splitr e) ltrD.
Qed.

Lemma scale_continuous : continuous (fun z : K^o * V => z.1 *: z.2).
Proof.
move=> [/= k x]; apply/cvg_ballP => e e0 /=.
near +oo_K => M.
pose r := `|e| / 2 / M.
exists (ball k r, ball x r).
  by split; apply: nbhsx_ballx; rewrite !divr_gt0// normr_gt0// gt_eqF.
rewrite -ball_normE /ball/= => lz /= [nk nx].
have := @ball_split _ _ (k *: lz.2)  (k *: x)  (lz.1 *: lz.2) `|e|.
rewrite -ball_normE /= real_lter_normr ?gtr0_real//.
rewrite (_ : _ < - e = false) ?orbF; last by rewrite ltr_nnorml// oppr_le0 ltW.
apply.
  rewrite -scalerBr normrZ -(@ltr_pM2r _ M^-1) ?invr_gt0//.
  by rewrite (le_lt_trans _ nx)// mulrC ler_pdivrMl// ler_wpM2r// invr_gt0.
rewrite -scalerBl normrZ.
rewrite (@le_lt_trans _ _ (`|k - lz.1| * M)) ?ler_wpM2l -?ltr_pdivlMr//.
rewrite (@le_trans _ _ (`|lz.2| + `|x|)) ?lerDl//.
rewrite (@le_trans _ _ (`|x| + (`|x| + r)))//.
  rewrite addrC lerD// -lerBlDl -(normrN x) (le_trans (lerB_normD _ _))//.
  by rewrite distrC ltW.
rewrite [leRHS](_ : _ = M^-1 * (M *  M)); last first.
  by rewrite mulrA mulVf ?mul1r// gt_eqF.
rewrite [leLHS](_ : _ = M^-1 * (M * (`|x| + `|x|) + `|e| / 2)); last first.
  by rewrite mulrDr mulrA mulVf ?mul1r ?gt_eqF// mulrC addrA.
by rewrite ler_wpM2l ?invr_ge0// ?ltW// -ltrBrDl -mulrBr ltr_pM// ltrBrDl.
Unshelve. all: by end_near. Qed.

Lemma locally_convex :
  exists2 B : set (set V), (forall b, b \in B -> convex b) & basis B.
Proof.
exists [set B | exists x r, B = ball x r].
  move=> b; rewrite inE /= => [[x]] [r] -> z y l.
  rewrite !inE -!ball_normE /= => zx yx l0; rewrite -subr_gt0 => l1.
  have -> : x = l *: x + (1 - l) *: x by rewrite addrC scalerBl subrK scale1r.
  rewrite [X in `|X|](_ : _ = l *: (x - z) + (1 - l) *: (x - y)); last first.
    by rewrite opprD addrACA -scalerBr -scalerBr.
  rewrite (@le_lt_trans _ _ (`|l| * `|x - z| + `|1 - l| * `|x - y|))//.
    by rewrite -!normrZ ler_normD.
  rewrite (@lt_le_trans _ _ (`|l| * r + `|1 - l| * r ))//.
    rewrite ltr_leD//.
      by rewrite -ltr_pdivlMl ?mulrA ?mulVf ?mul1r // ?normrE ?gt_eqF.
    by rewrite -ler_pdivlMl ?mulrA ?mulVf ?mul1r ?ltW // ?normrE ?gt_eqF.
  by rewrite !gtr0_norm// -mulrDl addrC subrK mul1r.
split.
  move=> B [x] [r] ->.
  rewrite openE/= -ball_normE/= /interior => y /= bxy; rewrite -nbhs_ballE.
  exists (r - `|x - y|) => /=; first by rewrite subr_gt0.
  move=> z; rewrite -ball_normE/= ltrBrDr.
  by apply: le_lt_trans; rewrite [in leRHS]addrC ler_distD.
move=> x B; rewrite -nbhs_ballE/= => -[r] r0 Bxr /=.
by exists (ball x r) => //; split; [exists x, r|exact: ballxx].
Qed.

HB.instance Definition _ :=
 Uniform_isTvs.Build K V add_continuous scale_continuous locally_convex.

HB.instance Definition _ :=
  PseudoMetricNormedZmod_Tvs_isNormedModule.Build K V normrZ.

HB.end.

Section standard_topology.
Variable R : numFieldType.
HB.instance Definition _ := Num.NormedZmodule.on R^o.

HB.instance Definition _ := NormedZmod_PseudoMetric_eq.Build R R^o erefl.
HB.instance Definition _ :=
  PseudoMetricNormedZmod_Tvs_isNormedModule.Build R R^o (@normrM _).

End standard_topology.

Lemma ball_itv {R : realFieldType} (x r : R) :
  ball x r = `]x - r, x + r[%classic.
Proof.
rewrite -(@ball_normE _ R^o) /ball_ set_itvE.
by apply/seteqP; split => t/=; rewrite ltr_distlC.
Qed.

Module numFieldNormedType.

Section realType.
Variable (R : realType).
#[export, non_forgetful_inheritance]
HB.instance Definition _ := GRing.ComAlgebra.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := Vector.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := NormedModule.copy R R^o.
End realType.

Section rcfType.
Variable (R : rcfType).
#[export, non_forgetful_inheritance]
HB.instance Definition _ := GRing.ComAlgebra.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := Vector.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := NormedModule.copy R R^o.
End rcfType.

Section archiFieldType.
Variable (R : archiFieldType).
#[export, non_forgetful_inheritance]
HB.instance Definition _ := GRing.ComAlgebra.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := Vector.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := NormedModule.copy R R^o.
End archiFieldType.

Section realFieldType.
Variable (R : realFieldType).
#[export, non_forgetful_inheritance]
HB.instance Definition _ := GRing.ComAlgebra.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := Vector.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := NormedModule.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := Num.RealField.on R.
End realFieldType.

Section numClosedFieldType.
Variable (R : numClosedFieldType).
#[export, non_forgetful_inheritance]
HB.instance Definition _ := GRing.ComAlgebra.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := Vector.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := NormedModule.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := Num.ClosedField.on R.
End numClosedFieldType.

Section numFieldType.
Variable (R : numFieldType).
#[export, non_forgetful_inheritance]
HB.instance Definition _ := GRing.ComAlgebra.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := Vector.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := NormedModule.copy R R^o.
#[export, non_forgetful_inheritance]
HB.instance Definition _ := Num.NumField.on R.
End numFieldType.

Module Exports. Export numFieldTopology.Exports. HB.reexport. End Exports.

End numFieldNormedType.
Import numFieldNormedType.Exports.

Lemma scaler1 {R : numFieldType} h : h%:A = h :> R.
Proof. by rewrite /GRing.scale/= mulr1. Qed.

Lemma limf_esup_dnbhsN {R : realType} (f : R -> \bar R) (a : R) :
  limf_esup f a^' = limf_esup (fun x => f (- x)%R) (- a)%R^'.
Proof.
rewrite /limf_esup dnbhsN image_comp/=.
congr (ereal_inf [set _ | _ in _]); apply/funext => A /=.
rewrite image_comp/= -compA (_ : _ \o _ = idfun)// funeqE => x/=.
by rewrite opprK.
Qed.

Section NormedModule_numDomainType.
Variables (R : numDomainType) (V : normedModType R).

Lemma normrZV (x : V) : `|x| \in GRing.unit -> `| `| x |^-1 *: x | = 1.
Proof. by move=> nxu; rewrite normrZ normrV// normr_id mulVr. Qed.

End NormedModule_numDomainType.

Section NormedModule_numFieldType.
Variables (R : numFieldType) (V : normedModType R).

Lemma normfZV (x : V) : x != 0 -> `| `|x|^-1 *: x | = 1.
Proof. by rewrite -normr_eq0 -unitfE => /normrZV->. Qed.

End NormedModule_numFieldType.

Section PseudoNormedZmod_numDomainType.
Variables (R : numDomainType) (V : pseudoMetricNormedZmodType R).

Local Notation ball_norm := (ball_ (@normr R V)).

Local Notation nbhs_ball := (@nbhs_ball _ V).

Local Notation nbhs_norm := (nbhs_ball_ ball_norm).

(* if we do not give the V argument to nbhs, the universally quantified set that
appears inside the notation for cvg_to has type
set (let '{| PseudoMetricNormedZmodule.sort := T |} := V in T) instead of set V,
which causes an inference problem in derive.v *)
Lemma nbhs_nbhs_norm : nbhs_norm = nbhs.
Proof. by rewrite ball_normE funeqE => x; rewrite -filter_from_ballE. Qed.

Lemma nbhs_normP x (P : V -> Prop) : (\near x, P x) <-> nbhs_norm x P.
Proof. by rewrite nbhs_nbhs_norm. Qed.

Lemma nbhs_le_nbhs_norm (x : V) : @nbhs V _ x `=>` nbhs_norm x.
Proof. by move=> P [e e0 subP]; apply/nbhs_normP; exists e. Qed.

Lemma nbhs_norm_le_nbhs x : nbhs_norm x `=>` nbhs x.
Proof. by move=> P /nbhs_normP [e e0 Pxe]; exists e. Qed.

Lemma filter_from_norm_nbhs x :
  @filter_from R _ [set x : R | 0 < x] (ball_norm x) = nbhs x.
Proof. by rewrite -nbhs_nbhs_norm ball_normE. Qed.

Lemma nbhs_normE (x : V) (P : V -> Prop) :
  nbhs_norm x P = \near x, P x.
Proof. by rewrite nbhs_nbhs_norm near_simpl. Qed.

Lemma filter_from_normE (x : V) (P : V -> Prop) :
  @filter_from R _ [set x : R | 0 < x] (ball_norm x) P = \near x, P x.
Proof. by rewrite filter_from_norm_nbhs. Qed.

Lemma near_nbhs_norm (x : V) (P : V -> Prop) :
  (\forall x \near nbhs_norm x, P x) = \near x, P x.
Proof. exact: nbhs_normE. Qed.

Lemma nbhs_norm_ball_norm x (e : {posnum R}) :
  nbhs_norm x (ball_norm x e%:num).
Proof. by rewrite ball_normE; exists e%:num => /=. Qed.

Lemma nbhs_ball_norm (x : V) (eps : {posnum R}) : nbhs x (ball_norm x eps%:num).
Proof. rewrite -nbhs_nbhs_norm; apply: nbhs_norm_ball_norm. Qed.

Lemma ball_norm_dec x y (e : R) : {ball_norm x e y} + {~ ball_norm x e y}.
Proof. exact: pselect. Qed.

Lemma ball_norm_sym x y (e : R) : ball_norm x e y -> ball_norm y e x.
Proof. by rewrite /ball_norm/= -opprB normrN. Qed.

Lemma ball_norm_le x (e1 e2 : R) :
  e1 <= e2 -> ball_norm x e1 `<=` ball_norm x e2.
Proof. by move=> e1e2 y /lt_le_trans; apply. Qed.

Let nbhs_simpl := (nbhs_simpl,@nbhs_nbhs_norm,@filter_from_norm_nbhs).

Lemma fcvgrPdist_lt {F : set_system V} {FF : Filter F} (y : V) :
  F --> y <-> forall eps, 0 < eps -> \forall y' \near F, `|y - y'| < eps.
Proof. by rewrite -filter_fromP /= !nbhs_simpl. Qed.

Lemma cvgrPdist_lt {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y <-> forall eps, 0 < eps -> \forall t \near F, `|y - f t| < eps.
Proof. exact: fcvgrPdist_lt. Qed.

Lemma cvgrPdistC_lt {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y <-> forall eps, 0 < eps -> \forall t \near F, `|f t - y| < eps.
Proof.
by rewrite cvgrPdist_lt; under eq_forall do under eq_near do rewrite distrC.
Qed.

Lemma cvgr_dist_lt {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y -> forall eps, eps > 0 -> \forall t \near F, `|y - f t| < eps.
Proof. by move=> /cvgrPdist_lt. Qed.

Lemma cvgr_distC_lt {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y -> forall eps, eps > 0 -> \forall t \near F, `|f t - y| < eps.
Proof. by move=> /cvgrPdistC_lt. Qed.

Lemma cvgr_dist_le {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y -> forall eps, eps > 0 -> \forall t \near F, `|y - f t| <= eps.
Proof.
by move=> ? ? ?; near do rewrite ltW//; apply: cvgr_dist_lt.
Unshelve. all: by end_near. Qed.

Lemma cvgr_distC_le {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y -> forall eps, eps > 0 -> \forall t \near F, `|f t - y| <= eps.
Proof.
by move=> ? ? ?; near do rewrite ltW//; apply: cvgr_distC_lt.
Unshelve. all: by end_near. Qed.

Lemma nbhs_norm0P {P : V -> Prop} :
  (\forall x \near 0, P x) <->
  filter_from [set e | 0 < e] (fun e => [set y | `|y| < e]) P.
Proof.
rewrite nbhs_normP; split=> -[/= e e0 Pe];
by exists e => // y /=; have /= := Pe y; rewrite distrC subr0.
Qed.

Lemma cvgr0Pnorm_lt {T} {F : set_system T} {FF : Filter F} (f : T -> V) :
  f @ F --> 0 <-> forall eps, 0 < eps -> \forall t \near F, `|f t| < eps.
Proof.
by rewrite cvgrPdistC_lt; under eq_forall do under eq_near do rewrite subr0.
Qed.

Lemma cvgr0_norm_lt {T} {F : set_system T} {FF : Filter F} (f : T -> V) :
  f @ F --> 0 -> forall eps, eps > 0 -> \forall t \near F, `|f t| < eps.
Proof. by move=> /cvgr0Pnorm_lt. Qed.

Lemma cvgr0_norm_le {T} {F : set_system T} {FF : Filter F} (f : T -> V) :
  f @ F --> 0 -> forall eps, eps > 0 -> \forall t \near F, `|f t| <= eps.
Proof.
by move=> ? ? ?; near do rewrite ltW//; apply: cvgr0_norm_lt.
Unshelve. all: by end_near. Qed.

Lemma nbhs0_lt e : 0 < e -> \forall x \near (0 : V), `|x| < e.
Proof. exact: cvgr0_norm_lt. Qed.

Lemma dnbhs0_lt e : 0 < e -> \forall x \near (0 : V)^', `|x| < e.
Proof. by move=> e_gt0; apply: cvg_within; apply: nbhs0_lt. Qed.

Lemma nbhs0_le e : 0 < e -> \forall x \near (0 : V), `|x| <= e.
Proof. exact: cvgr0_norm_le. Qed.

Lemma dnbhs0_le e : 0 < e -> \forall x \near (0 : V)^', `|x| <= e.
Proof. by move=> e_gt0; apply: cvg_within; apply: nbhs0_le. Qed.

Lemma nbhs_norm_ball x (eps : {posnum R}) : nbhs_norm x (ball x eps%:num).
Proof. by rewrite nbhs_nbhs_norm; exact: nbhsx_ballx. Qed.

Lemma nbhsDl (P : set V) (x y : V) :
  (\forall z \near (x + y), P z) <-> (\near x, P (x + y)).
Proof.
split=> /nbhs_normP[_/posnumP[e]/= Px]; apply/nbhs_normP; exists e%:num => //=.
  by move=> z /= xze; apply: Px; rewrite /= [z + y]addrC addrKA.
by move=> z /= xyz; rewrite -[z](addrNK y); apply: Px; rewrite /= opprB addrA.
Qed.

Lemma nbhsDr (P : set V) x y :
  (\forall z \near (x + y), P z) <-> (\near y, P (x + y)).
Proof. by rewrite addrC nbhsDl -propeqE; apply: eq_near => ?; rewrite addrC. Qed.

Lemma nbhs0P (P : set V) x : (\near x, P x) <-> (\forall e \near 0, P (x + e)).
Proof. by rewrite -nbhsDr addr0. Qed.

End PseudoNormedZmod_numDomainType.
#[global] Hint Resolve normr_ge0 : core.
Arguments cvgr_dist_lt {_ _ _ F FF}.
Arguments cvgr_distC_lt {_ _ _ F FF}.
Arguments cvgr_dist_le {_ _ _ F FF}.
Arguments cvgr_distC_le {_ _ _ F FF}.
Arguments cvgr0_norm_lt {_ _ _ F FF}.
Arguments cvgr0_norm_le {_ _ _ F FF}.

#[global] Hint Extern 0 (is_true (`|_ - ?x| < _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr_dist_lt end : core.
#[global] Hint Extern 0 (is_true (`|?x - _| < _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr_distC_lt end : core.
#[global] Hint Extern 0 (is_true (`|?x| < _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr0_norm_lt end : core.
#[global] Hint Extern 0 (is_true (`|_ - ?x| <= _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr_dist_le end : core.
#[global] Hint Extern 0 (is_true (`|?x - _| <= _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr_distC_le end : core.
#[global] Hint Extern 0 (is_true (`|?x| <= _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr0_norm_le end : core.

Section open_closed_sets.
(* TODO: duplicate theory within the subspace topology of Num.real
         in a numDomainType *)
Variable R : realFieldType.

(** Some open sets of R *)
Lemma open_lt (y : R) : open [set x : R| x < y].
Proof.
move=> x /=; rewrite -subr_gt0 => yDx_gt0. exists (y - x) => // z.
by rewrite /= ltr_distlC addrCA subrr addr0 => /andP[].
Qed.
Hint Resolve open_lt : core.

Lemma open_gt (y : R) : open [set x : R | x > y].
Proof.
move=> x /=; rewrite -subr_gt0 => xDy_gt0; exists (x - y) => // z.
by rewrite /= ltr_distlC subKr => /andP[].
Qed.
Hint Resolve open_gt : core.

Lemma open_neq (y : R) : open [set x : R | x != y].
Proof.
rewrite (_ : mkset _ = [set x | x < y] `|` [set x | x > y]); first exact: openU.
rewrite predeqE => x /=.
by rewrite eq_le negb_and -!ltNge orbC; symmetry; apply (rwP orP).
Qed.

Lemma interval_open a b : ~~ bound_side true a -> ~~ bound_side false b ->
  open [set x : R^o | x \in Interval a b].
Proof.
move: a b => [[]a|[]] [[]b|[]]// _ _.
- have -> : [set x | a < x < b] = [set x | a < x] `&` [set x | x < b].
    by rewrite predeqE => r; rewrite /mkset; split => [/andP[? ?] //|[-> ->]].
  by apply openI; [exact: open_gt | exact: open_lt].
- by under eq_set do rewrite itv_ge// inE.
- by under eq_set do rewrite in_itv andbT/=; exact: open_gt.
- exact: open_lt.
- by rewrite (_ : mkset _ = setT); [exact: openT | rewrite predeqE].
Qed.

(** Some closed sets of R *)
(* TODO: we can probably extend these results to numFieldType
   by adding a precondition that y \is Num.real *)
Lemma closed_le (y : R) : closed [set x : R | x <= y].
Proof.
rewrite (_ : mkset _ = ~` [set x | x > y]); first exact: open_closedC.
by rewrite predeqE => x /=; rewrite leNgt; split => /negP.
Qed.

Lemma closed_ge (y : R) : closed [set x : R | y <= x].
Proof.
rewrite (_ : mkset _ = ~` [set x | x < y]); first exact: open_closedC.
by rewrite predeqE => x /=; rewrite leNgt; split => /negP.
Qed.

Lemma closed_eq (y : R) : closed [set x : R | x = y].
Proof.
rewrite [X in closed X](_ : (eq^~ _) = ~` (xpredC (eq_op^~ y))).
  by apply: open_closedC; exact: open_neq.
by rewrite predeqE /setC => x /=; rewrite (rwP eqP); case: eqP; split.
Qed.

Lemma interval_closed a b : ~~ bound_side false a -> ~~ bound_side true b ->
  closed [set x : R^o | x \in Interval a b].
Proof.
move: a b => [[]a|[]] [[]b|[]]// _ _;
  do ?by under eq_set do rewrite itv_ge// inE falseE; apply: closed0.
- have -> : `[a, b]%classic = [set x | x >= a] `&` [set x | x <= b].
    by rewrite predeqE => ?; rewrite /= in_itv/=; split=> [/andP[]|[->]].
  by apply closedI; [exact: closed_ge | exact: closed_le].
- by under eq_set do rewrite in_itv andbT/=; exact: closed_ge.
- exact: closed_le.
Qed.

End open_closed_sets.

#[global] Hint Extern 0 (open _) => now apply: open_gt : core.
#[global] Hint Extern 0 (open _) => now apply: open_lt : core.
#[global] Hint Extern 0 (open _) => now apply: open_neq : core.
#[global] Hint Extern 0 (closed _) => now apply: closed_ge : core.
#[global] Hint Extern 0 (closed _) => now apply: closed_le : core.
#[global] Hint Extern 0 (closed _) => now apply: closed_eq : core.
#[global] Hint Extern 0 (open _) => now apply: interval_open : core.

Section at_left_right.
Variable R : numFieldType.

Definition at_left (x : R) := within (fun u => u < x) (nbhs x).
Definition at_right (x : R) := within (fun u => x < u) (nbhs x).
Local Notation "x ^'-" := (at_left x) : classical_set_scope.
Local Notation "x ^'+" := (at_right x) : classical_set_scope.

Global Instance at_right_proper_filter (x : R) : ProperFilter x^'+.
Proof.
apply: Build_ProperFilter => -[_/posnumP[d] /(_ (x + d%:num / 2))].
apply; last by rewrite ltrDl.
by rewrite /= opprD addNKr normrN ger0_norm// gtr_pMr// invf_lt1// ltr1n.
Qed.

Global Instance at_left_proper_filter (x : R) : ProperFilter x^'-.
Proof.
apply: Build_ProperFilter => -[_ /posnumP[d] /(_ (x - d%:num / 2))].
apply; last by rewrite gtrBl.
by rewrite /= opprB addrC subrK ger0_norm// gtr_pMr// invf_lt1// ltr1n.
Qed.

Lemma nbhs_right0P x (P : set R) :
  (\forall y \near x^'+, P y) <-> \forall e \near 0^'+, P (x + e).
Proof.
rewrite !near_withinE !near_simpl nbhs0P -propeqE.
by apply: (@eq_near _ (nbhs (0 : R))) => y; rewrite ltrDl.
Qed.

Lemma nbhs_left0P x (P : set R) :
  (\forall y \near x^'-, P y) <-> \forall e \near 0^'+, P (x - e).
Proof.
rewrite !near_withinE !near_simpl nbhs0P; split=> Px.
  rewrite -oppr0 nearN; near=> e; rewrite ltrN2 opprK => e_lt0.
  by apply: (near Px) => //; rewrite gtrDl.
by rewrite -oppr0 nearN; near=> e; rewrite gtrDl oppr_lt0; apply: (near Px).
Unshelve. all: by end_near. Qed.

Lemma nbhs_right_leftP (p : R) (P : pred R) :
  (\forall x \near (- p)^'+, (P \o -%R) x) <-> (\forall x \near p^'-, P x).
Proof.
by rewrite nbhs_right0P nbhs_left0P; split;
  apply: filterS=> r/=; rewrite opprD opprK.
Qed.

Lemma nbhs_right_gt x : \forall y \near x^'+, x < y.
Proof. by rewrite near_withinE; apply: nearW. Qed.

Lemma nbhs_left_lt x : \forall y \near x^'-, y < x.
Proof. by rewrite near_withinE; apply: nearW. Qed.

Lemma nbhs_right_neq x : \forall y \near x^'+, y != x.
Proof. by rewrite near_withinE; apply: nearW => ? /gt_eqF->. Qed.

Lemma nbhs_left_neq x : \forall y \near x^'-, y != x.
Proof. by rewrite near_withinE; apply: nearW => ? /lt_eqF->. Qed.

Lemma nbhs_right_ge x : \forall y \near x^'+, x <= y.
Proof. by rewrite near_withinE; apply: nearW; apply/ltW. Qed.

Lemma nbhs_left_le x : \forall y \near x^'-, y <= x.
Proof. by rewrite near_withinE; apply: nearW => ?; apply/ltW. Qed.

Lemma nbhs_right_lt x z : x < z -> \forall y \near x^'+, y < z.
Proof.
move=> xz; exists (z - x) => //=; first by rewrite subr_gt0.
by move=> y /= + xy; rewrite distrC ?ger0_norm ?subr_ge0 1?ltW// ltrD2r.
Qed.

Lemma nbhs_right_ltW x z : x < z -> \forall y \near nbhs x^'+, y <= z.
Proof.
by move=> xz; near=> y; apply/ltW; near: y; exact: nbhs_right_lt.
Unshelve. all: by end_near. Qed.

Lemma nbhs_right_ltDr x e : 0 < e -> \forall y \near x ^'+, y - x < e.
Proof.
move=> e0; near=> y; rewrite ltrBlDr; near: y.
by apply: nbhs_right_lt; rewrite ltrDr.
Unshelve. all: by end_near. Qed.

Lemma nbhs_right_le x z : x < z -> \forall y \near x^'+, y <= z.
Proof. by move=> xz; near do apply/ltW; apply: nbhs_right_lt.
Unshelve. all: by end_near. Qed.

Lemma nbhs_left_gt x z : z < x -> \forall y \near x^'-, z < y.
Proof.
move=> xz; rewrite nbhs_left0P; near do rewrite -ltrN2 opprB ltrBlDl.
by apply: nbhs_right_lt; rewrite subr_gt0.
Unshelve. all: by end_near. Qed.

Lemma nbhs_left_ge x z : z < x -> \forall y \near x^'-, z <= y.
Proof.
by move=> xz; near do apply/ltW; apply: nbhs_left_gt.
Unshelve. all: by end_near. Qed.

Lemma nbhs_left_ltBl x e : 0 < e -> \forall y \near x^'-, x - y < e.
Proof.
move=> e0; near=> y; rewrite -ltrBrDl ltrNl opprB; near: y.
by apply: nbhs_left_gt; rewrite ltrBlDr ltrDl.
Unshelve. all: by end_near. Qed.

Lemma withinN (A : set R) a :
  within A (nbhs (- a)) = - x @[x --> within (-%R @` A) (nbhs a)].
Proof.
rewrite eqEsubset /=; split; move=> E /= [e e0 aeE]; exists e => //.
  move=> r are ra; apply: aeE; last by rewrite memNE opprK.
  by rewrite /= opprK addrC distrC.
move=> r aer ar; rewrite -(opprK r); apply: aeE; last by rewrite -memNE.
by rewrite /= opprK -normrN opprD.
Qed.

Let fun_predC (T : choiceType) (f : T -> T) (p : pred T) : involutive f ->
  [set f x | x in p] = [set x | x in p \o f].
Proof.
by move=> fi; apply/seteqP; split => _/= [y hy <-];
  exists (f y) => //; rewrite fi.
Qed.

Lemma at_rightN a : (- a)^'+ = -%R @ a^'-.
Proof.
rewrite /at_right withinN [X in within X _](_ : _ = [set u | u < a])//.
rewrite (@fun_predC _ -%R)/=; last exact: opprK.
by rewrite image_id; under eq_fun do rewrite ltrNl opprK.
Qed.

Lemma at_leftN a : (- a)^'- = -%R @ a^'+.
Proof.
rewrite /at_left withinN [X in within X _](_ : _ = [set u | a < u])//.
rewrite (@fun_predC _ -%R)/=; last exact: opprK.
by rewrite image_id; under eq_fun do rewrite ltrNl opprK.
Qed.

(* NB: In not_near_at_rightP (and not_near_at_rightP), R has type numFieldType.
  It is possible realDomainType could make the proof simpler and at least as
  useful. *)
Lemma not_near_at_rightP (p : R) (P : pred R) :
  ~ (\forall x \near p^'+, P x) <->
  forall e : {posnum R}, exists2 x, p < x < p + e%:num & ~ P x.
Proof.
split=> [pPf e|ex_notPx].
- apply: contrapT => /forallPNP peP; apply: pPf; near=> t.
  apply: contrapT; apply: peP; apply/andP; split.
  + by near: t; exact: nbhs_right_gt.
  + by near: t; apply: nbhs_right_lt; rewrite ltrDl.
- rewrite /at_right near_withinE nearE.
  rewrite -filter_from_ballE /filter_from/= -forallPNP => _ /posnumP[d].
  have [x /andP[px xpd] notPx] := ex_notPx d; rewrite -existsNP; exists x => /=.
  apply: contra_not notPx; apply => //.
  by rewrite /ball/= ltr0_norm ?subr_lt0// opprB ltrBlDl.
Unshelve. all: by end_near. Qed.

Lemma not_near_at_leftP (p : R) (P : pred R) :
  ~ (\forall x \near p^'-, P x) <->
  forall e : {posnum R}, exists2 x : R, p - e%:num < x < p & ~ P x.
Proof.
rewrite -nbhs_right_leftP not_near_at_rightP; split => + e => /(_ e)[r pre Pr].
- by exists (- r) => //; rewrite ltrNr andbC ltrNl opprB addrC.
- by exists (- r) => /=; rewrite ?opprK// ltrN2 ltrNl opprD opprK andbC.
Qed.

End at_left_right.
#[global] Typeclasses Opaque at_left at_right.
Notation "x ^'-" := (at_left x) : classical_set_scope.
Notation "x ^'+" := (at_right x) : classical_set_scope.

#[global] Hint Extern 0 (Filter (nbhs _^'+)) =>
  (apply: at_right_proper_filter) : typeclass_instances.

#[global] Hint Extern 0 (Filter (nbhs _^'-)) =>
  (apply: at_left_proper_filter) : typeclass_instances.

Lemma cvg_at_leftNP {T : topologicalType} {R : numFieldType}
    (f : R -> T) a (l : T) :
  f @ a^'- --> l <-> f \o -%R @ (- a)^'+ --> l.
Proof.
by rewrite at_rightN -?fmap_comp; under [_ \o _]eq_fun => ? do rewrite /= opprK.
Qed.

Lemma cvg_at_rightNP {T : topologicalType} {R : numFieldType}
    (f : R -> T) a (l : T) :
  f @ a^'+ --> l <-> f \o -%R @ (- a)^'- --> l.
Proof.
by rewrite at_leftN -?fmap_comp; under [_ \o _]eq_fun => ? do rewrite /= opprK.
Qed.

Lemma cvgNy_compNP {T : topologicalType} {R : numFieldType} (f : R -> T)
    (l : set_system T) :
  f x @[x --> -oo] --> l <-> (f \o -%R) x @[x --> +oo] --> l.
Proof.
have f_opp : f =1 (fun x => (f \o -%R) (- x)) by move=> x; rewrite /comp opprK.
by rewrite (eq_cvg -oo _ f_opp) fmap_comp ninftyN.
Qed.
#[deprecated(since="mathcomp-analysis 1.9.0", note="renamed to `cvgNy_compNP`")]
Notation cvgyNP := cvgNy_compNP (only parsing).

Lemma cvgy_compNP {T : topologicalType} {R : numFieldType} (f : R -> T)
    (l : set_system T) :
  f x @[x --> +oo] --> l <-> (f \o -%R) x @[x --> -oo] --> l.
Proof.
have f_opp : f =1 (fun x => (f \o -%R) (- x)) by move=> x; rewrite /comp opprK.
by rewrite (eq_cvg +oo _ f_opp) fmap_comp ninfty.
Qed.

Section open_itv_subset.
Context {R : realType}.
Variables (A : set R) (x : R).

Lemma open_itvoo_subset :
  open A -> A x -> \forall r \near 0^'+, `]x - r, x + r[ `<=` A.
Proof.
move=> /[apply] -[] _/posnumP[r] /subset_ball_prop_in_itv xrA.
exists r%:num => //= k; rewrite /= distrC subr0 set_itvoo => /ltr_normlW kr k0.
by apply/(subset_trans _ xrA)/subset_itvW; apply/ltW;
  [rewrite ler_ltB | rewrite ler_ltD].
Qed.

Lemma open_itvcc_subset :
  open A -> A x -> \forall r \near 0^'+, `[x - r, x + r] `<=` A.
Proof.
move=> /[apply] -[] _/posnumP[r].
have -> : r%:num = 2 * (r%:num / 2) by rewrite mulrCA divff// mulr1.
move/subset_ball_prop_in_itvcc => /= xrA; exists (r%:num / 2) => //= k.
rewrite /= distrC subr0 set_itvcc => /ltr_normlW kr k0.
move=> z /andP [xkz zxk]; apply: xrA => //; rewrite in_itv/=; apply/andP; split.
  by rewrite (le_trans _ xkz)// lerB// ltW.
by rewrite (le_trans zxk)// lerD// ltW.
Qed.

End open_itv_subset.

Section at_left_right_topologicalType.
Variables (R : numFieldType) (V : topologicalType) (f : R -> V) (x : R).

Lemma cvg_at_right_filter (l : V) :
  f z @[z --> x] --> l -> f z @[z --> x^'+] --> l.
Proof. exact: (@cvg_within_filter _ _ _ (nbhs x)). Qed.

Lemma cvg_at_left_filter (l : V) :
  f z @[z --> x] --> l -> f z @[z --> x^'-] --> l.
Proof. exact: (@cvg_within_filter _ _ _ (nbhs x)). Qed.

Lemma cvg_at_right_within : f x @[x --> x^'+] --> f x ->
  f x @[x --> within (fun u => x <= u) (nbhs x)] --> f x.
Proof.
move=> fxr U Ux; rewrite ?near_simpl ?near_withinE; near=> z; rewrite le_eqVlt.
by move/predU1P => [<-|]; [exact: nbhs_singleton | near: z; exact: fxr].
Unshelve. all: by end_near. Qed.

Lemma cvg_at_left_within : f x @[x --> x^'-] --> f x ->
  f x @[x --> within (fun u => u <= x) (nbhs x)] --> f x.
Proof.
move=> fxr U Ux; rewrite ?near_simpl ?near_withinE; near=> z; rewrite le_eqVlt.
by move/predU1P => [->|]; [exact: nbhs_singleton | near: z; exact: fxr].
Unshelve. all: by end_near. Qed.

End at_left_right_topologicalType.

Section at_left_right_pmNormedZmod.
Variables (R : numFieldType) (V : pseudoMetricNormedZmodType R).

Lemma nbhsr0P (P : set V) x :
  (\forall y \near x, P y) <->
  (\forall e \near 0^'+, forall y, `|x - y| <= e -> P y).
Proof.
rewrite nbhs0P/= near_withinE/= !near_simpl.
split=> /nbhs_norm0P[/= _/posnumP[e] /(_ _) Px]; apply/nbhs_norm0P.
  exists e%:num => //= r /= re yr y xyr; rewrite -[y](addrNK x) addrC.
  by apply: Px; rewrite /= distrC (le_lt_trans _ re)// gtr0_norm.
exists (e%:num / 2) => //= r /= re; apply: (Px (e%:num / 2)) => //=.
  by rewrite gtr0_norm// ltr_pdivrMr// ltr_pMr// ltr1n.
by rewrite opprD addNKr normrN ltW.
Qed.

Let cvgrP {F : set_system V} {FF : Filter F} (y : V) : [<->
  F --> y;
  forall eps, 0 < eps -> \forall t \near F, `|y - t| <= eps;
  \forall eps \near 0^'+, \forall t \near F, `|y - t| <= eps;
  \forall eps \near 0^'+, \forall t \near F, `|y - t| < eps].
Proof.
tfae; first by move=> *; apply: cvgr_dist_le.
- by move=> Fy; near do apply: Fy; apply: nbhs_right_gt.
- move=> Fy; near=> e; near (0:R)^'+ => d; near=> x.
  rewrite (@le_lt_trans _ _ d)//; first by near: x; near: d.
  by near: d; apply: nbhs_right_lt; near: e; apply: nbhs_right_gt.
- move=> Fy; apply/cvgrPdist_lt => e e_gt0; near (0:R)^'+ => d.
  near=> x; rewrite (@lt_le_trans _ _ d)//; first by near: x; near: d.
  by near: d; apply: nbhs_right_le.
Unshelve. all: by end_near. Qed.

Lemma cvgrPdist_le {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y <-> forall eps, 0 < eps -> \forall t \near F, `|y - f t| <= eps.
Proof. exact: (cvgrP _ 0 1)%N. Qed.

Lemma cvgrPdist_ltp {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y <-> \forall eps \near 0^'+, \forall t \near F, `|y - f t| < eps.
Proof. exact: (cvgrP _ 0 3)%N. Qed.

Lemma cvgrPdist_lep {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y <-> \forall eps \near 0^'+, \forall t \near F, `|y - f t| <= eps.
Proof. exact: (cvgrP _ 0 2)%N. Qed.

Lemma cvgrPdistC_le {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y <-> forall eps, 0 < eps -> \forall t \near F, `|f t - y| <= eps.
Proof.
rewrite cvgrPdist_le.
by under [X in X <-> _]eq_forall do under eq_near do rewrite distrC.
Qed.

Lemma cvgrPdistC_ltp {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y <-> \forall eps \near 0^'+, \forall t \near F, `|f t - y| < eps.
Proof.
by rewrite cvgrPdist_ltp; under eq_near do under eq_near do rewrite distrC.
Qed.

Lemma cvgrPdistC_lep {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y <-> \forall eps \near 0^'+, \forall t \near F, `|f t - y| <= eps.
Proof.
by rewrite cvgrPdist_lep; under eq_near do under eq_near do rewrite distrC.
Qed.

Lemma cvgr0Pnorm_le {T} {F : set_system T} {FF : Filter F} (f : T -> V) :
  f @ F --> 0 <-> forall eps, 0 < eps -> \forall t \near F, `|f t| <= eps.
Proof.
rewrite cvgrPdistC_le.
by under [X in X <-> _]eq_forall do under eq_near do rewrite subr0.
Qed.

Lemma cvgr0Pnorm_ltp {T} {F : set_system T} {FF : Filter F} (f : T -> V) :
  f @ F --> 0 <-> \forall eps \near 0^'+, \forall t \near F, `|f t| < eps.
Proof.
by rewrite cvgrPdistC_ltp; under eq_near do under eq_near do rewrite subr0.
Qed.

Lemma cvgr0Pnorm_lep {T} {F : set_system T} {FF : Filter F} (f : T -> V) :
  f @ F --> 0 <-> \forall eps \near 0^'+, \forall t \near F, `|f t| <= eps.
Proof.
by rewrite cvgrPdistC_lep; under eq_near do under eq_near do rewrite subr0.
Qed.

Lemma cvgr_norm_lt {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y -> forall u, `|y| < u -> \forall t \near F, `|f t| < u.
Proof.
move=> Fy z zy; near (0:R)^'+ => k; near=> x; have : `|f x - y| < k.
  by near: x; apply: cvgr_distC_lt => //; near: k; apply: nbhs_right_gt.
move=> /(le_lt_trans (ler_dist_dist _ _)) /real_ltr_normlW.
rewrite realB// ltrBlDl => /(_ _)/lt_le_trans; apply => //.
by rewrite -lerBrDl; near: k; apply: nbhs_right_le; rewrite subr_gt0.
Unshelve. all: by end_near. Qed.

Lemma cvgr_norm_le {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y -> forall u, `|y| < u -> \forall t \near F, `|f t| <= u.
Proof.
by move=> fy u yu; near do apply/ltW; apply: cvgr_norm_lt yu.
Unshelve. all: by end_near. Qed.

Lemma cvgr_norm_gt {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y -> forall u, `|y| > u -> \forall t \near F, `|f t| > u.
Proof.
move=> Fy z zy; near (0:R)^'+ => k; near=> x; have: `|f x - y| < k.
  by near: x; apply: cvgr_distC_lt => //; near: k; apply: nbhs_right_gt.
move=> /(le_lt_trans (ler_dist_dist _ _)); rewrite distrC => /real_ltr_normlW.
rewrite realB// ltrBlDl  -ltrBlDr => /(_ isT); apply: le_lt_trans.
rewrite lerBrDl -lerBrDr; near: k; apply: nbhs_right_le.
by rewrite subr_gt0.
Unshelve. all: by end_near. Qed.

Lemma cvgr_norm_ge {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y -> forall u, `|y| > u -> \forall t \near F, `|f t| >= u.
Proof.
by move=> fy u yu; near do apply/ltW; apply: cvgr_norm_gt yu.
Unshelve. all: by end_near. Qed.

Lemma cvgr_neq0 {T} {F : set_system T} {FF : Filter F} (f : T -> V) (y : V) :
  f @ F --> y -> y != 0 -> \forall t \near F, f t != 0.
Proof.
move=> Fy z; near do rewrite -normr_gt0.
by apply: (@cvgr_norm_gt _ _ _ _ y); rewrite // normr_gt0.
Unshelve. all: by end_near. Qed.

End at_left_right_pmNormedZmod.
Arguments cvgr_norm_lt {R V T F FF f}.
Arguments cvgr_norm_le {R V T F FF f}.
Arguments cvgr_norm_gt {R V T F FF f}.
Arguments cvgr_norm_ge {R V T F FF f}.
Arguments cvgr_neq0 {R V T F FF f}.

#[global] Hint Extern 0 (is_true (`|_ - ?x| < _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr_dist_lt end : core.
#[global] Hint Extern 0 (is_true (`|?x - _| < _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr_distC_lt end : core.
#[global] Hint Extern 0 (is_true (`|?x| < _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr0_norm_lt end : core.
#[global] Hint Extern 0 (is_true (`|_ - ?x| <= _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr_dist_le end : core.
#[global] Hint Extern 0 (is_true (`|?x - _| <= _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr_distC_le end : core.
#[global] Hint Extern 0 (is_true (`|?x| <= _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: cvgr0_norm_le end : core.

#[global] Hint Extern 0 (is_true (_ < ?x)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_right_gt end : core.
#[global] Hint Extern 0 (is_true (?x < _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_left_lt end : core.
#[global] Hint Extern 0 (is_true (?x != _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_right_neq end : core.
#[global] Hint Extern 0 (is_true (?x != _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_left_neq end : core.
#[global] Hint Extern 0 (is_true (_ < ?x)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_left_gt end : core.
#[global] Hint Extern 0 (is_true (?x < _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_right_lt end : core.
#[global] Hint Extern 0 (is_true (_ <= ?x)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_right_ge end : core.
#[global] Hint Extern 0 (is_true (?x <= _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_left_le end : core.
#[global] Hint Extern 0 (is_true (_ <= ?x)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_right_ge end : core.
#[global] Hint Extern 0 (is_true (?x <= _)) => match goal with
  H : x \is_near _ |- _ => near: x; exact: nbhs_left_le end : core.

#[global] Hint Extern 0 (ProperFilter _^'-) =>
  (apply: at_left_proper_filter) : typeclass_instances.
#[global] Hint Extern 0 (ProperFilter _^'+) =>
  (apply: at_right_proper_filter) : typeclass_instances.

Section at_left_rightR.
Variable (R : numFieldType).

Lemma real_cvgr_lt {T} {F : set_system T} {FF : Filter F} (f : T -> R) (y : R) :
    y \is Num.real -> f @ F --> y ->
  forall z, z > y -> \forall t \near F, f t \is Num.real -> f t < z.
Proof.
move=> yr Fy z zy; near=> x => fxr.
rewrite -(ltrD2r (- y)) real_ltr_normlW// ?rpredB//.
by near: x; apply: cvgr_distC_lt => //; rewrite subr_gt0.
Unshelve. all: by end_near. Qed.

Lemma real_cvgr_le {T} {F : set_system T} {FF : Filter F} (f : T -> R) (y : R) :
    y \is Num.real ->  f @ F --> y ->
  forall z, z > y -> \forall t \near F, f t \is Num.real -> f t <= z.
Proof.
move=> /real_cvgr_lt/[apply] + ? z0 => /(_ _ z0).
by apply: filterS => ? /[apply]/ltW.
Qed.

Lemma real_cvgr_gt {T} {F : set_system T} {FF : Filter F} (f : T -> R) (y : R) :
    y \is Num.real -> f @ F --> y ->
  forall z, y > z -> \forall t \near F, f t \is Num.real -> f t > z.
Proof.
move=> yr Fy z zy; near=> x => fxr.
rewrite -ltrN2 -(ltrD2l y) real_ltr_normlW// ?rpredB//.
by near: x; apply: cvgr_dist_lt => //; rewrite subr_gt0.
Unshelve. all: by end_near. Qed.

Lemma real_cvgr_ge {T} {F : set_system T} {FF : Filter F} (f : T -> R) (y : R) :
    y \is Num.real -> f @ F --> y ->
  forall z, z < y -> \forall t \near F, f t \is Num.real -> f t >= z.
Proof.
move=> /real_cvgr_gt/[apply] + ? z0 => /(_ _ z0).
by apply: filterS => ? /[apply]/ltW.
Qed.

End at_left_rightR.
Arguments real_cvgr_le {R T F FF f}.
Arguments real_cvgr_lt {R T F FF f}.
Arguments real_cvgr_ge {R T F FF f}.
Arguments real_cvgr_gt {R T F FF f}.

Section realFieldType.
Context (R : realFieldType).

Lemma at_right_in_segment (x : R) (P : set R) :
  (\forall e \near 0^'+, {in `[x - e, x + e], forall x, P x}) <-> (\near x, P x).
Proof.
rewrite nbhsr0P -propeqE; apply: eq_near => y /=.
by rewrite -propeqE; apply: eq_forall => z; rewrite ler_distlC.
Qed.

Lemma cvgr_lt {T} {F : set_system T} {FF : Filter F} (f : T -> R) (y : R) :
  f @ F --> y -> forall z, z > y -> \forall t \near F, f t < z.
Proof.
move=> Fy z zy; near=> x; rewrite -(ltrD2r (- y)) ltr_normlW//.
by near: x; apply: cvgr_distC_lt => //; rewrite subr_gt0.
Unshelve. all: by end_near. Qed.

Lemma cvgr_le {T} {F : set_system T} {FF : Filter F} (f : T -> R) (y : R) :
  f @ F --> y -> forall z, z > y -> \forall t \near F, f t <= z.
Proof.
by move=> /cvgr_lt + ? z0 => /(_ _ z0); apply: filterS => ?; apply/ltW.
Qed.

Lemma cvgr_gt {T} {F : set_system T} {FF : Filter F} (f : T -> R) (y : R) :
  f @ F --> y -> forall z, y > z -> \forall t \near F, f t > z.
Proof.
move=> Fy z zy; near=> x; rewrite -ltrN2 -(ltrD2l y) ltr_normlW//.
by near: x; apply: cvgr_dist_lt => //; rewrite subr_gt0.
Unshelve. all: by end_near. Qed.

Lemma cvgr_ge {T} {F : set_system T} {FF : Filter F} (f : T -> R) (y : R) :
  f @ F --> y -> forall z, z < y -> \forall t \near F, f t >= z.
Proof.
by move=> /cvgr_gt + ? z0 => /(_ _ z0); apply: filterS => ?; apply/ltW.
Qed.

End realFieldType.
Arguments cvgr_le {R T F FF f}.
Arguments cvgr_lt {R T F FF f}.
Arguments cvgr_ge {R T F FF f}.
Arguments cvgr_gt {R T F FF f}.

Definition self_sub (K : numDomainType) (V W : normedModType K)
  (f : V -> W) (x : V * V) : W := f x.1 - f x.2.
Arguments self_sub {K V W} f x /.

Definition fun1 {T : Type} {K : numFieldType} : T -> K := fun=> 1.
Arguments fun1 {T K} x /.

Definition dominated_by {T : Type} {K : numDomainType} {V W : pseudoMetricNormedZmodType K}
  (h : T -> V) (k : K) (f : T -> W) (F : set_system T) :=
  F [set x | `|f x| <= k * `|h x|].

Definition strictly_dominated_by {T : Type} {K : numDomainType} {V W : pseudoMetricNormedZmodType K}
  (h : T -> V) (k : K) (f : T -> W) (F : set_system T) :=
  F [set x | `|f x| < k * `|h x|].

Lemma sub_dominatedl (T : Type) (K : numDomainType)
    (V W : pseudoMetricNormedZmodType K)
    (h : T -> V) (k : K) (F G : set_system T) : F `=>` G ->
  (@dominated_by T K V W h k)^~ G `<=` (dominated_by h k)^~ F.
Proof. by move=> FG f; exact: FG. Qed.

Lemma sub_dominatedr (T : Type) (K : numDomainType)
    (V : pseudoMetricNormedZmodType K)
    (h : T -> V) (k : K) (f g : T -> V) (F : set_system T) (FF : Filter F) :
   (\forall x \near F, `|f x| <= `|g x|) ->
   dominated_by h k g F -> dominated_by h k f F.
Proof. by move=> le_fg; apply: filterS2 le_fg => x; apply: le_trans. Qed.

Lemma dominated_by1 {T : Type} {K : numFieldType}
    {V : pseudoMetricNormedZmodType K} :
  @dominated_by T K _ V fun1 = fun k f F => F [set x | `|f x| <= k].
Proof.
rewrite funeq3E => k f F.
by congr F; rewrite funeqE => x/=; rewrite normr1 mulr1.
Qed.

Lemma strictly_dominated_by1 {T : Type} {K : numFieldType}
    {V : pseudoMetricNormedZmodType K} :
  @strictly_dominated_by T K _ V fun1 = fun k f F => F [set x | `|f x| < k].
Proof.
rewrite funeq3E => k f F.
by congr F; rewrite funeqE => x/=; rewrite normr1 mulr1.
Qed.

Lemma ex_dom_bound {T : Type} {K : numFieldType}
    {V W : pseudoMetricNormedZmodType K}
    (h : T -> V) (f : T -> W) (F : set_system T) {PF : ProperFilter F}:
  (\forall M \near +oo, dominated_by h M f F) <->
  exists M, dominated_by h M f F.
Proof.
rewrite /dominated_by; split => [/pinfty_ex_gt0[M M_gt0]|[M]] FM.
  by exists M.
have [] := pselect (exists x, (h x != 0) && (`|f x| <= M * `|h x|)); last first.
  rewrite -forallNE => Nex; exists 0; split => //.
  move=> k k_gt0; apply: filterS FM => x /= f_le_Mh.
  have /negP := Nex x; rewrite negb_and negbK f_le_Mh orbF => /eqP h_eq0.
  by rewrite h_eq0 normr0 !mulr0 in f_le_Mh *.
case => x0 /andP[hx0_neq0] /(le_trans (normr_ge0 _)) /ger0_real.
rewrite realrM // ?normr_eq0// => M_real.
exists M; split => // k Mk; apply: filterS FM => x /le_trans/= ->//.
by rewrite ler_wpM2r// ltW.
Qed.

Lemma ex_strict_dom_bound {T : Type} {K : numFieldType}
    {V W : pseudoMetricNormedZmodType K}
    (h : T -> V) (f : T -> W) (F : set_system T) {PF : ProperFilter F} :
  (\forall x \near F, h x != 0) ->
  (\forall M \near +oo, dominated_by h M f F) <->
   exists M, strictly_dominated_by h M f F.
Proof.
move=> hN0; rewrite ex_dom_bound /dominated_by /strictly_dominated_by.
split => -[] M FM; last by exists M; apply: filterS FM => x /ltW.
exists (M + 1); apply: filterS2 hN0 FM => x hN0 /le_lt_trans/= ->//.
by rewrite ltr_pM2r ?normr_gt0// ltrDl.
Qed.

Definition bounded_near {T : Type} {K : numFieldType}
    {V : pseudoMetricNormedZmodType K}
  (f : T -> V) (F : set_system T) :=
  \forall M \near +oo, F [set x | `|f x| <= M].

Lemma boundedE {T : Type} {K : numFieldType} {V : pseudoMetricNormedZmodType K} :
  @bounded_near T K V = fun f F => \forall M \near +oo, dominated_by fun1 M f F.
Proof. by rewrite dominated_by1. Qed.

Lemma sub_boundedr (T : Type) (K : numFieldType) (V : pseudoMetricNormedZmodType K)
     (F G : set_system T) : F `=>` G ->
  (@bounded_near T K V)^~ G `<=` bounded_near^~ F.
Proof. by move=> FG f; rewrite /bounded_near; apply: filterS=> M; apply: FG. Qed.

Lemma sub_boundedl (T : Type) (K : numFieldType) (V : pseudoMetricNormedZmodType K)
     (f g : T -> V) (F : set_system T) (FF : Filter F) :
 (\forall x \near F, `|f x| <= `|g x|) ->  bounded_near g F -> bounded_near f F.
Proof.
move=> le_fg; rewrite /bounded_near; apply: filterS => M.
by apply: filterS2 le_fg => x; apply: le_trans.
Qed.

Lemma ex_bound {T : Type} {K : numFieldType} {V : pseudoMetricNormedZmodType K}
  (f : T -> V) (F : set_system T) {PF : ProperFilter F}:
  bounded_near f F <-> exists M, F [set x | `|f x| <= M].
Proof. by rewrite boundedE ex_dom_bound dominated_by1. Qed.

Lemma ex_strict_bound {T : Type} {K : numFieldType} {V : pseudoMetricNormedZmodType K}
  (f : T -> V) (F : set_system T) {PF : ProperFilter F}:
  bounded_near f F <-> exists M, F [set x | `|f x| < M].
Proof.
rewrite boundedE ex_strict_dom_bound ?strictly_dominated_by1//.
by near=> x; rewrite oner_eq0.
Unshelve. all: by end_near. Qed.

Lemma ex_strict_bound_gt0 {T : Type} {K : numFieldType} {V : pseudoMetricNormedZmodType K}
  (f : T -> V) (F : set_system T) {PF : Filter F}:
  bounded_near f F -> exists2 M, M > 0 & F [set x | `|f x| < M].
Proof.
move=> /pinfty_ex_gt0[M M_gt0 FM]; exists (M + 1); rewrite ?addr_gt0//.
by apply: filterS FM => x /le_lt_trans/= ->//; rewrite ltrDl.
Qed.

Notation "[ 'bounded' E | x 'in' A ]" :=
  (bounded_near (fun x => E) (globally A)).
Notation bounded_set := [set A | [bounded x | x in A]].
Notation bounded_fun := [set f | [bounded f x | x in setT]].

Lemma bounded_cst (K : numFieldType) {V : pseudoMetricNormedZmodType K}
  (k : V) T (A : set T) : [bounded k | _ in A].
Proof.
rewrite /bounded_near; near=> M => t At /=.
by near: M; exact: nbhs_pinfty_ge.
Unshelve. all: end_near. Qed.

Lemma bounded_fun_has_ubound (T : Type) (R : realFieldType) (a : T -> R) :
  bounded_fun a -> has_ubound (range a).
Proof.
move=> [M [Mreal]]/(_ (`|M| + 1)).
rewrite (le_lt_trans (ler_norm _)) ?ltrDl// => /(_ erefl) aM.
by exists (`|M| + 1) => _ [n _ <-]; rewrite (le_trans (ler_norm _))// aM.
Qed.

Lemma bounded_funN (T : Type) (R : realFieldType) (a : T -> R) :
  bounded_fun a -> bounded_fun (- a).
Proof.
move=> [M [Mreal aM]]; rewrite /bounded_fun /bounded_near; near=> x => y /= _.
by rewrite normrN; apply: aM.
Unshelve. all: by end_near. Qed.

Lemma bounded_fun_has_lbound (T : Type) (R : realFieldType) (a : T -> R) :
  bounded_fun a -> has_lbound (range a).
Proof.
move=> /bounded_funN/bounded_fun_has_ubound ba; apply/has_lb_ubN.
by apply: subset_has_ubound ba => _ [_ [n _] <- <-]; exists n.
Qed.

Lemma bounded_funD (T : Type) (R : realFieldType) (a b : T -> R) :
  bounded_fun a -> bounded_fun b -> bounded_fun (a \+ b).
Proof.
move=> [M [Mreal Ma]] [N [Nreal Nb]].
rewrite /bounded_fun/bounded_near; near=> x => y /= _.
rewrite (le_trans (ler_normD _ _))// [x]splitr.
by rewrite lerD// (Ma, Nb)// ltr_pdivlMr//;
   near: x; apply: nbhs_pinfty_gt; rewrite ?rpredM ?rpred_nat.
Unshelve. all: by end_near. Qed.

Lemma bounded_locally (T : topologicalType)
    (R : numFieldType) (V : normedModType R) (A : set T) (f : T -> V) :
  [bounded f x | x in A] -> [locally [bounded f x | x in A]].
Proof. by move=> /sub_boundedr AB x Ax; apply: AB; apply: within_nbhsW. Qed.

Notation "k .-lipschitz_on f" :=
  (dominated_by (self_sub id) k (self_sub f)) : type_scope.

Definition sub_klipschitz (K : numFieldType) (V W : normedModType K) (k : K)
           (f : V -> W) (F G : set_system (V * V)) :
  F `=>` G -> k.-lipschitz_on f G -> k.-lipschitz_on f F.
Proof. exact. Qed.

Definition lipschitz_on (K : numFieldType) (V W : normedModType K)
           (f : V -> W) (F : set_system (V * V)) :=
  \forall M \near +oo, M.-lipschitz_on f F.

Definition sub_lipschitz (K : numFieldType) (V W : normedModType K)
           (f : V -> W) (F G : set_system (V * V)) :
  F `=>` G -> lipschitz_on f G -> lipschitz_on f F.
Proof. by move=> FG; rewrite /lipschitz_on; apply: filterS => M; apply: FG. Qed.

Lemma klipschitzW (K : numFieldType) (V W : normedModType K) (k : K)
      (f : V -> W) (F : set_system (V * V)) {PF : ProperFilter F} :
  k.-lipschitz_on f F -> lipschitz_on f F.
Proof. by move=> f_lip; apply/ex_dom_bound; exists k. Qed.

Notation "k .-lipschitz_ A f" :=
  (k.-lipschitz_on f (globally (A `*` A))) : type_scope.
Notation "k .-lipschitz f" := (k.-lipschitz_setT f) : type_scope.
Notation "[ 'lipschitz' E | x 'in' A ]" :=
  (lipschitz_on (fun x => E) (globally (A `*` A))) : type_scope.
Notation lipschitz f := [lipschitz f x | x in setT].

Lemma lipschitz_set0 (K : numFieldType) (V W : normedModType K)
  (f : V -> W) : [lipschitz f x | x in set0].
Proof. by apply: nearW; rewrite setX0 => ?; apply: globally0. Qed.

Lemma lipschitz_set1 (K : numFieldType) (V W : normedModType K)
  (f : V -> W) (a : V) : [lipschitz f x | x in [set a]].
Proof.
apply: (@klipschitzW _ _ _ `|f a|).
  exact: (@globally_properfilter _ _ (a, a)).
by move=> [x y] /= [] -> ->; rewrite !subrr !normr0 mulr0.
Qed.

Lemma klipschitz_locally (R : numFieldType) (V W : normedModType R) (k : R)
    (f : V -> W) (A : set V) :
  k.-lipschitz_A f -> [locally k.-lipschitz_A f].
Proof. by move=> + x Ax; apply: sub_klipschitz; apply: within_nbhsW. Qed.

Lemma lipschitz_locally (R : numFieldType) (V W : normedModType R)
    (A : set V) (f : V -> W) :
  [lipschitz f x | x in A] -> [locally [lipschitz f x | x in A]].
Proof. by move=> + x Ax; apply: sub_lipschitz; apply: within_nbhsW. Qed.

Lemma lipschitz_id (R : numFieldType) (V : normedModType R) :
  1.-lipschitz (@id V).
Proof. by move=> [/= x y] _; rewrite mul1r. Qed.
Arguments lipschitz_id {R V}.

Section contractions.
Context {R : numDomainType} {X Y : normedModType R} {U : set X} {V : set Y}.

Definition contraction (q : {nonneg R}) (f : {fun U >-> V}) :=
  q%:num < 1 /\ q%:num.-lipschitz_U f.

Definition is_contraction (f : {fun U >-> V}) := exists q, contraction q f.

End contractions.

Lemma contraction_fixpoint_unique {R : realDomainType}
    {X : normedModType R} (U : set X) (f : {fun U >-> U}) (x y : X) :
  is_contraction f -> U x -> U y -> x = f x -> y = f y -> x = y.
Proof.
case => q [q1 ctrfq] Ux Uy fixx fixy; apply/subr0_eq/normr0_eq0/eqP.
have [->|xyneq] := eqVneq x y; first by rewrite subrr normr0.
have xypos : 0 < `|x - y| by rewrite normr_gt0 subr_eq0.
suff : `|x - y| <= q%:num * `|x - y| by rewrite ler_pMl // leNgt q1.
by rewrite [in leLHS]fixx [in leLHS]fixy; exact: (ctrfq (_, _)).
Qed.

Section PseudoNormedZMod_numFieldType.
Variables (R : numFieldType) (V : pseudoMetricNormedZmodType R).

Local Notation ball_norm := (ball_ (@normr R V)).

Local Notation nbhs_norm := (@nbhs_ball _ V).

Lemma norm_hausdorff : hausdorff_space V.
Proof.
rewrite ball_hausdorff => a b ab.
have ab2 : 0 < `|a - b| / 2 by apply divr_gt0 => //; rewrite normr_gt0 subr_eq0.
set r := PosNum ab2; exists (r, r) => /=.
apply/negPn/negP => /set0P[c] []; rewrite -ball_normE /ball_ => acr bcr.
have r22 : r%:num * 2 = r%:num + r%:num.
  by rewrite (_ : 2 = 1 + 1) // mulrDr mulr1.
move: (ltrD acr bcr); rewrite -r22 (distrC b c).
move/(le_lt_trans (ler_distD c a b)).
by rewrite -mulrA mulVr ?mulr1 ?ltxx // unitfE.
Qed.
Hint Extern 0 (hausdorff_space _) => solve[apply: norm_hausdorff] : core.

(* TODO: check if the following lemma are indeed useless *)
(*       i.e. where the generic lemma is applied, *)
(*            check that norm_hausdorff is not used in a hard way *)

Lemma norm_closeE (x y : V): close x y = (x = y). Proof. exact: closeE. Qed.
Lemma norm_close_eq (x y : V) : close x y -> x = y. Proof. exact: close_eq. Qed.

Lemma norm_cvg_unique {F} {FF : ProperFilter F} : is_subset1 [set x : V | F --> x].
Proof. exact: cvg_unique. Qed.

Lemma norm_cvg_eq (x y : V) : x --> y -> x = y. Proof. exact: (@cvg_eq V). Qed.
Lemma norm_lim_id (x : V) : lim (nbhs x) = x. Proof. exact: lim_id. Qed.

Lemma norm_cvg_lim {F} {FF : ProperFilter F} (l : V) : F --> l -> lim F = l.
Proof. exact: (@cvg_lim V). Qed.

Lemma norm_lim_near_cst U {F} {FF : ProperFilter F} (l : V) (f : U -> V) :
   (\forall x \near F, f x = l) -> lim (f @ F) = l.
Proof. exact: lim_near_cst. Qed.

Lemma norm_lim_cst U {F} {FF : ProperFilter F} (k : V) :
   lim ((fun _ : U => k) @ F) = k.
Proof. exact: lim_cst. Qed.

Lemma norm_cvgi_unique {U : Type} {F} {FF : ProperFilter F} (f : U -> set V) :
  {near F, is_fun f} -> is_subset1 [set x : V | f `@ F --> x].
Proof. exact: cvgi_unique. Qed.

Lemma norm_cvgi_lim {U} {F} {FF : ProperFilter F} (f : U -> V -> Prop) (l : V) :
  F (fun x : U => is_subset1 (f x)) ->
  f `@ F --> l -> lim (f `@ F) = l.
Proof. exact: cvgi_lim. Qed.

Lemma distm_lt_split (z x y : V) (e : R) :
  `|x - z| < e / 2 -> `|z - y| < e / 2 -> `|x - y| < e.
Proof. by have := @ball_split _ _ z x y e; rewrite -ball_normE. Qed.

Lemma distm_lt_splitr (z x y : V) (e : R) :
  `|z - x| < e / 2 -> `|z - y| < e / 2 -> `|x - y| < e.
Proof. by have := @ball_splitr _ _ z x y e; rewrite -ball_normE. Qed.

Lemma distm_lt_splitl (z x y : V) (e : R) :
  `|x - z| < e / 2 -> `|y - z| < e / 2 -> `|x - y| < e.
Proof. by have := @ball_splitl _ _ z x y e; rewrite -ball_normE. Qed.

Lemma normm_leW (x : V) (e : R) : e > 0 -> `|x| <= e / 2 -> `|x| < e.
Proof.
by move=> /posnumP[{}e] /le_lt_trans ->//; rewrite [ltRHS]splitr ltr_pwDl.
Qed.

Lemma normm_lt_split (x y : V) (e : R) :
  `|x| < e / 2 -> `|y| < e / 2 -> `|x + y| < e.
Proof.
by move=> xlt ylt; rewrite -[y]opprK (@distm_lt_split 0) ?subr0 ?opprK ?add0r.
Qed.

End PseudoNormedZMod_numFieldType.

Section NormedModule_numFieldType.
Variables (R : numFieldType) (V : normedModType R).

Section cvgr_norm_infty.
Variables (I : Type) (F : set_system I) (FF : Filter F) (f : I -> V) (y : V).

Lemma cvgr_norm_lty :
  f @ F --> y -> \forall M \near +oo, \forall y' \near F, `|f y'| < M.
Proof. by move=> Fy; near do exact: (cvgr_norm_lt y).
Unshelve. all: by end_near. Qed.

Lemma cvgr_norm_ley :
  f @ F --> y -> \forall M \near +oo, \forall y' \near F, `|f y'| <= M.
Proof.
by move=> Fy; near do exact: (cvgr_norm_le y).
Unshelve. all: by end_near. Qed.

Lemma cvgr_norm_gtNy :
  f @ F --> y -> \forall M \near -oo, \forall y' \near F, `|f y'| > M.
Proof.
by move=> Fy; near do exact: (cvgr_norm_gt y).
Unshelve. all: by end_near. Qed.

Lemma cvgr_norm_geNy :
  f @ F --> y -> \forall M \near -oo, \forall y' \near F, `|f y'| >= M.
Proof.
by move=> Fy; near do exact: (cvgr_norm_ge y).
Unshelve. all: by end_near. Qed.

End cvgr_norm_infty.

Lemma cvg_bounded {I} {F : set_system I} {FF : Filter F} (f : I -> V) (y : V) :
  f @ F --> y -> bounded_near f F.
Proof. exact: cvgr_norm_ley. Qed.

End NormedModule_numFieldType.
Arguments cvgr_norm_lty {R V I F FF}.
Arguments cvgr_norm_ley {R V I F FF}.
Arguments cvgr_norm_gtNy {R V I F FF}.
Arguments cvgr_norm_geNy {R V I F FF}.
Arguments cvg_bounded {R V I F FF}.
#[global]
Hint Extern 0 (hausdorff_space _) => solve[apply: norm_hausdorff] : core.

Module Export NbhsNorm.
Definition nbhs_simpl := (nbhs_simpl,@nbhs_nbhs_norm,@filter_from_norm_nbhs).
End NbhsNorm.

Lemma cvg_at_rightE (R : numFieldType) (V : normedModType R) (f : R -> V) x :
  cvg (f @ x^') -> lim (f @ x^') = lim (f @ x^'+).
Proof.
move=> cvfx; apply/Logic.eq_sym.
apply: (@cvg_lim _ _ _ (at_right _)) => // A /cvfx /nbhs_ballP [_ /posnumP[e] xe_A].
by exists e%:num => //= y xe_y; rewrite lt_def => /andP [xney _]; apply: xe_A.
Qed.
Arguments cvg_at_rightE {R V} f x.

Lemma cvg_at_leftE (R : numFieldType) (V : normedModType R) (f : R -> V) x :
  cvg (f @ x^') -> lim (f @ x^') = lim (f @ x^'-).
Proof.
move=> cvfx; apply/Logic.eq_sym.
apply: (@cvg_lim _ _ _ (at_left _)) => // A /cvfx /nbhs_ballP [_ /posnumP[e] xe_A].
exists e%:num => //= y xe_y; rewrite lt_def => /andP [xney _].
by apply: xe_A => //; rewrite eq_sym.
Qed.
Arguments cvg_at_leftE {R V} f x.

Section continuous_within_itvP.
Context {R : realType}.
Implicit Type f : R -> R.

Let near_at_left (a : itv_bound R) b f eps : (a < BLeft b)%O -> 0 < eps ->
  {within [set` Interval a (BRight b)], continuous f} ->
  \forall t \near b^'-, normr (f b - f t) < eps.
Proof.
move=> ab eps_gt0 cf.
move/continuous_withinNx/cvgrPdist_lt/(_ _ eps_gt0) : (cf b).
rewrite /dnbhs/= near_withinE !near_simpl /prop_near1 /nbhs/=.
rewrite -nbhs_subspace_in//; last first.
  rewrite /= in_itv/= lexx andbT.
  by move: a ab {cf} => [[a|a]/=|[|]//]; rewrite bnd_simp// => /ltW.
rewrite /within/= near_simpl; apply: filter_app.
move: a ab {cf} => [a0 a/= /[!bnd_simp] ab|[_|//]].
- exists (b - a); rewrite /= ?subr_gt0// => c cba + ac.
  apply=> //; rewrite ?lt_eqF// !in_itv/= (ltW ac)/= andbT; move: cba => /=.
  rewrite gtr0_norm ?subr_gt0// ltrD2l ltrNr opprK => {}ac.
  by case: a0 => //=; exact/ltW.
- by exists 1%R => //= c cb1 + bc; apply; rewrite ?lt_eqF ?in_itv/= ?ltW.
Qed.

Let near_at_right a (b : itv_bound R) f eps : (BRight a < b)%O -> 0 < eps ->
  {within [set` Interval (BLeft a) b], continuous f} ->
  \forall t \near a^'+, normr (f a - f t) < eps.
Proof.
move=> ab eps_gt0 cf.
move/continuous_withinNx/cvgrPdist_lt/(_ _ eps_gt0) : (cf a).
rewrite /dnbhs/= near_withinE !near_simpl// /prop_near1 /nbhs/=.
rewrite -nbhs_subspace_in//; last first.
  rewrite /= in_itv/= lexx//=.
  by move: b ab {cf} => [[b|b]/=|[|]//]; rewrite bnd_simp// => /ltW.
rewrite /within/= near_simpl; apply: filter_app.
move: b ab {cf} => [b0 b/= /[!bnd_simp] ab|[//|_]].
- exists (b - a); rewrite /= ?subr_gt0// => c cba + ac.
  apply=> //; rewrite ?gt_eqF// !in_itv/= (ltW ac)/=; move: cba => /=.
  rewrite ltr0_norm ?subr_lt0// opprB ltrD2r.
  by case: b0 => //= /ltW.
- by exists 2%R => //= c ca1 + ac; apply; rewrite ?gt_eqF ?in_itv/= ?ltW.
Qed.

Lemma continuous_within_itvP a b f : a < b ->
  {within `[a, b], continuous f} <->
  [/\ {in `]a, b[, continuous f}, f @ a^'+ --> f a & f @b^'- --> f b].
Proof.
move=> ab; split=> [abf|].
  split; [apply/in_continuous_mksetP|apply/cvgrPdist_lt => eps eps_gt0 /=..].
  - rewrite -continuous_open_subspace; last exact: interval_open.
    by move: abf; exact/continuous_subspaceW/subset_itvW.
  - by apply: near_at_right => //; rewrite bnd_simp.
  - by apply: near_at_left => //; rewrite bnd_simp.
case=> ctsoo ctsL ctsR; apply/subspace_continuousP => x /andP[].
rewrite !bnd_simp/= !le_eqVlt => /predU1P[<-{x}|ax] /predU1P[|].
- by move/eqP; rewrite lt_eqF.
- move=> _; apply/cvgrPdist_lt => eps eps_gt0 /=.
  move/cvgrPdist_lt/(_ _ eps_gt0): ctsL; rewrite /at_right !near_withinE.
  apply: filter_app; exists (b - a); rewrite /= ?subr_gt0// => c cba + ac.
  have : a <= c by move: ac => /andP[].
  by rewrite le_eqVlt => /predU1P[->|/[swap] /[apply]//]; rewrite subrr normr0.
- move=> ->; apply/cvgrPdist_lt => eps eps_gt0 /=.
  move/cvgrPdist_lt/(_ _ eps_gt0): ctsR; rewrite /at_left !near_withinE.
  apply: filter_app; exists (b - a); rewrite /= ?subr_gt0 // => c cba + ac.
  have : c <= b by move: ac => /andP[].
  by rewrite le_eqVlt => /predU1P[->|/[swap] /[apply]//]; rewrite subrr normr0.
- move=> xb; have aboox : x \in `]a, b[ by rewrite !in_itv/= ax.
  rewrite within_interior; first exact: ctsoo.
  suff : `]a, b[ `<=` interior `[a, b] by exact.
  by rewrite -open_subsetE; [exact: subset_itvW| exact: interval_open].
Qed.

Lemma continuous_within_itvcyP a (f : R -> R) :
  {within `[a, +oo[, continuous f} <->
  {in `]a, +oo[, continuous f} /\ f x @[x --> a^'+] --> f a.
Proof.
split=> [cf|].
  split; [apply/in_continuous_mksetP|apply/cvgrPdist_lt => eps eps_gt0 /=].
  - rewrite -continuous_open_subspace; last exact: interval_open.
    by apply: continuous_subspaceW cf => ?; rewrite /= !in_itv !andbT/= => /ltW.
  - by apply: near_at_right => //; rewrite bnd_simp.
move=> [cf fa]; apply/subspace_continuousP => x /andP[].
rewrite bnd_simp/= le_eqVlt => /predU1P[<-{x}|ax] _.
- apply/cvgrPdist_lt => eps eps_gt0/=; move/cvgrPdist_lt/(_ _ eps_gt0) : fa.
  rewrite /at_right !near_withinE; apply: filter_app.
  exists 1%R => //= c c1a /[swap]; rewrite in_itv/= andbT le_eqVlt.
  by move=> /predU1P[->|/[swap]/[apply]//]; rewrite subrr normr0.
- have xaoo : x \in `]a, +oo[ by rewrite in_itv/= andbT.
  rewrite within_interior; first exact: cf.
  suff : `]a, +oo[ `<=` interior `[a, +oo[ by exact.
  rewrite -open_subsetE; last exact: interval_open.
  by move=> ?/=; rewrite !in_itv/= !andbT; exact: ltW.
Qed.

Lemma continuous_within_itvNycP b (f : R -> R) :
  {within `]-oo, b], continuous f} <->
  {in `]-oo, b[, continuous f} /\ f x @[x --> b^'-] --> f b.
Proof.
split=> [cf|].
  split; [apply/in_continuous_mksetP|apply/cvgrPdist_lt => eps eps_gt0 /=].
  - rewrite -continuous_open_subspace; last exact: interval_open.
    by apply: continuous_subspaceW cf => ?/=; rewrite !in_itv/=; exact: ltW.
  - by apply: near_at_left => //; rewrite bnd_simp.
move=> [cf fb]; apply/subspace_continuousP => x /andP[_].
rewrite bnd_simp/= le_eqVlt=> /predU1P[->{x}|xb].
- apply/cvgrPdist_lt => eps eps_gt0/=; move/cvgrPdist_lt/(_ _ eps_gt0) : fb.
  rewrite /at_right !near_withinE; apply: filter_app.
  exists 1%R => //= c c1b /[swap]; rewrite in_itv/= le_eqVlt.
  by move=> /predU1P[->|/[swap]/[apply]//]; rewrite subrr normr0.
- have xb_i : x \in `]-oo, b[ by rewrite in_itv/=.
  rewrite within_interior; first exact: cf.
  suff : `]-oo, b[ `<=` interior `]-oo, b] by exact.
  rewrite -open_subsetE; last exact: interval_open.
  by move=> ?/=; rewrite !in_itv/=; exact: ltW.
Qed.

End continuous_within_itvP.

Lemma within_continuous_continuous {R : realType} a b (f : R -> R) x : (a < b)%R ->
  {within `[a, b], continuous f} -> x \in `]a, b[ -> {for x, continuous f}.
Proof.
by move=> ab /continuous_within_itvP-/(_ ab)[+ _] /[swap] xab cf; exact.
Qed.

(* TODO: generalize to R : numFieldType *)
Section hausdorff.

Lemma pseudoMetricNormedZModType_hausdorff (R : realFieldType)
    (V : pseudoMetricNormedZmodType R) :
  hausdorff_space V.
Proof.
move=> p q clp_q; apply/subr0_eq/normr0_eq0/Rhausdorff => A B pq_A.
rewrite -(@normr0 _ V) -(subrr p) => pp_B.
suff loc_preim r C : nbhs`|p - r| C ->
    nbhs r ((fun r => `|p - r|) @^-1` C).
  have [r []] := clp_q _ _ (loc_preim _ _ pp_B) (loc_preim _ _ pq_A).
  by exists `|p - r|.
move=> [e egt0 pre_C]; apply: nbhs_le_nbhs_norm; exists e => //= s /= rse.
apply: pre_C; apply: le_lt_trans (ler_dist_dist _ _) _.
by rewrite opprB addrC subrKA distrC.
Qed.

End hausdorff.

Module Export NearNorm.
Definition near_simpl := (@near_simpl, @nbhs_normE, @filter_from_normE,
  @near_nbhs_norm).
Ltac near_simpl := rewrite ?near_simpl.
End NearNorm.

(** Matrices *)
Section mx_norm.
Variables (K : numDomainType) (m n : nat).
Implicit Types x y : 'M[K]_(m, n).

Definition mx_norm x : K := (\big[maxr/0%:nng]_i `|x i.1 i.2|%:nng)%:num.

Lemma mx_normE x : mx_norm x = (\big[maxr/0%:nng]_i `|x i.1 i.2|%:nng)%:num.
Proof. by []. Qed.

Lemma ler_mx_norm_add x y : mx_norm (x + y) <= mx_norm x + mx_norm y.
Proof.
rewrite !mx_normE [_ <= _%:num]num_le; apply/bigmax_leP.
split=> [|ij _]; first exact: addr_ge0.
rewrite mxE; apply: le_trans (ler_normD _ _) _.
by rewrite lerD// -[leLHS]nngE num_le; exact: le_bigmax.
Qed.

Lemma mx_norm_eq0 x : mx_norm x = 0 -> x = 0.
Proof.
move/eqP; rewrite eq_le -[0]nngE mx_normE num_le => /andP[/bigmax_leP[_ x0] _].
apply/matrixP => i j; rewrite mxE; apply/eqP.
by rewrite -num_abs_eq0 eq_le (x0 (i, j))//= -num_le/=.
Qed.

Lemma mx_norm0 : mx_norm 0 = 0.
Proof.
rewrite /mx_norm (eq_bigr (fun=> 0%R%:nng)) /=.
  by elim/big_ind : _ => // a b; rewrite num_max => -> ->; rewrite maxxx.
by move=> i _; apply val_inj => /=; rewrite mxE normr0.
Qed.

Lemma mx_norm_neq0 x : mx_norm x != 0 -> exists i, mx_norm x = `|x i.1 i.2|.
Proof.
rewrite /mx_norm.
elim/big_ind : _ => [|a b Ha Hb H|/= i _ _]; [by rewrite eqxx| |by exists i].
case: (leP a b) => ab.
+ suff /Hb[i xi] : b%:num != 0 by exists i.
  by apply: contra H => b0; rewrite max_r.
+ suff /Ha[i xi] : a%:num != 0 by exists i.
  by apply: contra H => a0; rewrite max_l // ltW.
Qed.

Lemma mx_norm_natmul x k : mx_norm (x *+ k) = (mx_norm x) *+ k.
Proof.
rewrite [in RHS]/mx_norm; elim: k => [|k ih]; first by rewrite !mulr0n mx_norm0.
rewrite !mulrS; apply/eqP; rewrite eq_le; apply/andP; split.
  by rewrite -ih; exact/ler_mx_norm_add.
have [/mx_norm_eq0->|x0] := eqVneq (mx_norm x) 0.
  by rewrite -/(mx_norm 0) -/(mx_norm 0) !(mul0rn,addr0,mx_norm0).
rewrite -/(mx_norm x) -num_abs_le; last by rewrite mx_normE.
apply/bigmax_geP; right => /=.
have [i Hi] := mx_norm_neq0 x0.
exists i => //; rewrite Hi -!mulrS -normrMn mulmxnE.
by rewrite le_eqVlt; apply/orP; left; apply/eqP/val_inj => /=; rewrite normr_id.
Qed.

Lemma mx_normN x : mx_norm (- x) = mx_norm x.
Proof.
congr (_%:nngnum).
by apply eq_bigr => /= ? _; apply/eqP; rewrite mxE -num_eq //= normrN.
Qed.

End mx_norm.

Lemma mx_normrE (K : realDomainType) (m n : nat) (x : 'M[K]_(m, n)) :
  mx_norm x = \big[maxr/0]_ij `|x ij.1 ij.2|.
Proof.
rewrite /mx_norm; apply/esym.
elim/big_ind2 : _ => //= a a' b b' ->{a'} ->{b'}.
by have [ab|ab] := leP a b; [rewrite max_r | rewrite max_l // ltW].
Qed.

HB.instance Definition _ (K : numDomainType) (m n : nat) :=
  Num.Zmodule_isNormed.Build K 'M[K]_(m, n)
    (@ler_mx_norm_add _ _ _) (@mx_norm_eq0 _ _ _)
    (@mx_norm_natmul _ _ _) (@mx_normN _ _ _).

Section matrix_NormedModule.
Variables (K : numFieldType) (m n : nat).

Local Lemma ball_gt0 (x y : 'M[K]_(m.+1, n.+1)) e : ball x e y -> 0 < e.
Proof. by move/(_ ord0 ord0); apply: le_lt_trans. Qed.

Lemma mx_norm_ball : @ball _ 'M[K]_(m.+1, n.+1) = ball_ (fun x => `| x |).
Proof.
rewrite /normr /ball_ predeq3E => x e y /=; rewrite mx_normE; split => xey.
- have e_gt0 : 0 < e := ball_gt0 xey.
  move: e_gt0 (e_gt0) xey => /ltW/nonnegP[{}e] e_gt0 xey.
  rewrite num_lt; apply/bigmax_ltP => /=.
  by rewrite -num_lt /=; split => // -[? ?] _; rewrite !mxE; exact: xey.
- have e_gt0 : 0 < e by rewrite (le_lt_trans _ xey).
  move: e_gt0 (e_gt0) xey => /ltW/nonnegP[{}e] e_gt0.
  move=> /(bigmax_ltP _ _ _ (fun _ => _%:itv)) /= [e0 xey] i j.
  by move: (xey (i, j)); rewrite !mxE; exact.
Qed.

HB.instance Definition _ :=
  NormedZmod_PseudoMetric_eq.Build K 'M[K]_(m.+1, n.+1) mx_norm_ball.

Lemma mx_normZ (l : K) (x : 'M[K]_(m.+1, n.+1)) : `| l *: x | = `| l | * `| x |.
Proof.
rewrite {1 3}/normr /= !mx_normE
 (eq_bigr (fun i => (`|l| * `|x i.1 i.2|)%:nng)); last first.
  by move=> i _; rewrite mxE //=; apply/eqP; rewrite -num_eq /= normrM.
elim/big_ind2 : _ => // [|a b c d bE dE]; first by rewrite mulr0.
by rewrite !num_max bE dE maxr_pMr.
Qed.

HB.instance Definition _ :=
  PseudoMetricNormedZmod_Lmodule_isNormedModule.Build K 'M[K]_(m.+1, n.+1)
    mx_normZ.

End matrix_NormedModule.

(** Pairs *)
Section prod_PseudoMetricNormedZmodule.
Context {K : numDomainType} {U V : pseudoMetricNormedZmodType K}.

Lemma ball_prod_normE : ball = ball_ (fun x => `| x : U * V |).
Proof.
rewrite funeq2E => - [xu xv] e; rewrite predeqE => - [yu yv].
rewrite /ball /= /prod_ball -!ball_normE /ball_ /=.
by rewrite comparable_gt_max// ?real_comparable//; split=> /andP.
Qed.

Lemma prod_norm_ball : @ball _ (U * V)%type = ball_ (fun x => `|x|).
Proof. by rewrite /= - ball_prod_normE. Qed.

HB.instance Definition _ := NormedZmod_PseudoMetric_eq.Build K (U * V)%type
  prod_norm_ball.

End prod_PseudoMetricNormedZmodule.

Section prod_NormedModule.
Context {K : numFieldType} {U V : normedModType K}.

Lemma prod_norm_scale (l : K) (x : U * V) : `| l *: x | = `|l| * `| x |.
Proof. by rewrite prod_normE /= !normrZ maxr_pMr. Qed.

HB.instance Definition _ :=
  PseudoMetricNormedZmod_Tvs_isNormedModule.Build K (U * V)%type
  prod_norm_scale.

End prod_NormedModule.

Section example_of_sharing.
Variables (K : numDomainType).

Example matrix_triangle m n (M N : 'M[K]_(m.+1, n.+1)) :
  `|M + N| <= `|M| + `|N|.
Proof. exact: ler_normD. Qed.

Example pair_triangle (x y : K * K) : `|x + y| <= `|x| + `|y|.
Proof. exact: ler_normD. Qed.

End example_of_sharing.

Section prod_NormedModule_lemmas.

Context {T : Type} {K : numDomainType} {U V : normedModType K}.

Lemma fcvgr2dist_ltP {F : set_system U} {G : set_system V}
  {FF : Filter F} {FG : Filter G} (y : U) (z : V) :
  (F, G) --> (y, z) <->
  forall eps, 0 < eps ->
   \forall y' \near F & z' \near G, `| (y, z) - (y', z') | < eps.
Proof. exact: fcvgrPdist_lt. Qed.

Lemma cvgr2dist_ltP {I J} {F : set_system I} {G : set_system J}
  {FF : Filter F} {FG : Filter G} (f : I -> U) (g : J -> V) (y : U) (z : V) :
  (f @ F, g @ G) --> (y, z) <->
  forall eps, 0 < eps ->
   \forall i \near F & j \near G, `| (y, z) - (f i, g j) | < eps.
Proof.
rewrite fcvgr2dist_ltP; split=> + e e0 => /(_ e e0);
  by rewrite !near_simpl// => ?; rewrite !near_simpl.
Qed.

Lemma cvgr2dist_lt {I J} {F : set_system I} {G : set_system J}
  {FF : Filter F} {FG : Filter G} (f : I -> U) (g : J -> V) (y : U) (z : V) :
  (f @ F, g @ G) --> (y, z) ->
  forall eps, 0 < eps ->
   \forall i \near F & j \near G, `| (y, z) - (f i, g j) | < eps.
Proof. by rewrite cvgr2dist_ltP. Qed.

End prod_NormedModule_lemmas.
Arguments cvgr2dist_ltP {_ _ _ _ _ F G FF FG}.
Arguments cvgr2dist_lt {_ _ _ _ _ F G FF FG}.

(** Normed vector spaces have some continuous functions that are in fact
continuous on pseudoMetricNormedZmodType *)
Section NVS_continuity_pseudoMetricNormedZmodType.
Context {K : numFieldType} {V : pseudoMetricNormedZmodType K}.

Lemma opp_continuous : continuous (@GRing.opp V).
Proof.
move=> x; apply/cvgrPdist_lt=> e e0; near do rewrite -opprD normrN.
exact: cvgr_dist_lt.
Unshelve. all: by end_near. Qed.

Lemma add_continuous : continuous (fun z : V * V => z.1 + z.2).
Proof.
move=> [/= x y]; apply/cvgrPdist_lt=> _/posnumP[e]; near=> a b => /=.
by rewrite opprD addrACA normm_lt_split.
Unshelve. all: by end_near. Qed.

Lemma natmul_continuous n : continuous (fun x : V => x *+ n).
Proof.
case: n => [|n] x; first exact: cvg_cst.
apply/cvgrPdist_lt=> _/posnumP[e]; near=> a.
by rewrite -mulrnBl normrMn -mulr_natr -ltr_pdivlMr.
Unshelve. all: by end_near. Qed.

Lemma norm_continuous : continuous (normr : V -> K).
Proof.
move=> x; apply/cvgrPdist_lt => e e0; apply/nbhs_normP; exists e => //= y.
exact/le_lt_trans/ler_dist_dist.
Qed.

End NVS_continuity_pseudoMetricNormedZmodType.

Section NVS_continuity_normedModType.
Context {K : numFieldType} {V : normedModType K}.

Lemma scale_continuous : continuous (fun z : K * V => z.1 *: z.2).
Proof.
move=> [/= k x]; apply/cvgrPdist_lt => _/posnumP[e]; near +oo_K => M.
near=> l z => /=; have M0 : 0 < M by [].
rewrite (@distm_lt_split _ _ (k *: z)) // -?(scalerBr, scalerBl) normrZ.
  rewrite (@le_lt_trans _ _ (M * `|x - z|)) ?ler_wpM2r -?ltr_pdivlMl//.
  by near: z; apply: cvgr_dist_lt; rewrite // mulr_gt0 ?invr_gt0.
rewrite (@le_lt_trans _ _ (`|k - l| * M)) ?ler_wpM2l -?ltr_pdivlMr//.
  by near: z; near: M; apply: cvg_bounded (@cvg_refl _ _).
by near: l; apply: cvgr_dist_lt; rewrite // divr_gt0.
Unshelve. all: by end_near. Qed.

Arguments scale_continuous _ _ : clear implicits.

Lemma scaler_continuous k : continuous (fun x : V => k *: x).
Proof.
by move=> x; apply: (cvg_comp2 (cvg_cst _) cvg_id (scale_continuous (_, _))).
Qed.

Lemma scalel_continuous (x : V) : continuous (fun k : K => k *: x).
Proof.
by move=> k; apply: (cvg_comp2 cvg_id (cvg_cst _) (scale_continuous (_, _))).
Qed.

(** Continuity of norm *)
End NVS_continuity_normedModType.

Section NVS_continuity_mul.

Context {K : numFieldType}.

Lemma mul_continuous : continuous (fun z : K * K => z.1 * z.2).
Proof. exact: scale_continuous. Qed.

Lemma mulrl_continuous (x : K) : continuous ( *%R x).
Proof. exact: scaler_continuous. Qed.

Lemma mulrr_continuous (y : K) : continuous ( *%R^~ y : K -> K).
Proof. exact: scalel_continuous. Qed.

Lemma inv_continuous (x : K) : x != 0 -> {for x, continuous (@GRing.inv K)}.
Proof.
move=> x_neq0; have nx_gt0 : `|x| > 0 by rewrite normr_gt0.
apply/(@cvgrPdist_ltp _ _ _ (nbhs x)); near (0 : K)^'+ => d. near=> e.
near=> y; have y_neq0 : y != 0 by near: y; apply: (cvgr_neq0 x).
rewrite /= -div1r -[y^-1]div1r -mulNr addf_div// mul1r mulN1r normrM normfV.
rewrite ltr_pdivrMr ?normr_gt0 ?mulf_neq0// (@lt_le_trans _ _ (e * d))//.
  by near: y;  apply: cvgr_distC_lt => //; rewrite mulr_gt0.
rewrite ler_pM2l => //=; rewrite normrM -ler_pdivrMl//.
near: y; apply: (cvgr_norm_ge x) => //; rewrite ltr_pdivrMl//.
by near: d; apply: nbhs_right_lt; rewrite mulr_gt0.
Unshelve. all: by end_near. Qed.

End NVS_continuity_mul.

Section cvg_composition_pseudometric.
Context {K : numFieldType} {V : pseudoMetricNormedZmodType K} {T : Type}.
Context (F : set_system T) {FF : Filter F}.
Implicit Types (f g : T -> V) (s : T -> K) (k : K) (x : T) (a b : V).

Lemma cvgN f a : f @ F --> a -> - f @ F --> - a.
Proof. by move=> ?; apply: continuous_cvg => //; exact: opp_continuous. Qed.

Lemma cvgNP f a : - f @ F --> - a <-> f @ F --> a.
Proof. by split=> /cvgN//; rewrite !opprK. Qed.

Lemma is_cvgN f : cvg (f @ F) -> cvg (- f @ F).
Proof. by move=> /cvgN /cvgP. Qed.

Lemma is_cvgNE f : cvg ((- f) @ F) = cvg (f @ F).
Proof. by rewrite propeqE; split=> /cvgN; rewrite ?opprK => /cvgP. Qed.

Lemma cvgMn f n a : f @ F --> a -> ((@GRing.natmul _)^~n \o f) @ F --> a *+ n.
Proof. by move=> ?;  apply: continuous_cvg => //; exact: natmul_continuous. Qed.

Lemma is_cvgMn f n : cvg (f @ F) -> cvg (((@GRing.natmul _)^~n \o f) @ F).
Proof. by move=> /cvgMn /cvgP. Qed.

Lemma cvgD f g a b : f @ F --> a -> g @ F --> b -> (f + g) @ F --> a + b.
Proof. by move=> ? ?; apply: continuous2_cvg => //; apply add_continuous. Qed.

Lemma is_cvgD f g : cvg (f @ F) -> cvg (g @ F) -> cvg (f + g @ F).
Proof. by have := cvgP _ (cvgD _ _); apply. Qed.

Lemma cvgB f g a b : f @ F --> a -> g @ F --> b -> (f - g) @ F --> a - b.
Proof. by move=> ? ?; apply: cvgD => //; apply: cvgN. Qed.

Lemma is_cvgB f g : cvg (f @ F) -> cvg (g @ F) -> cvg (f - g @ F).
Proof. by have := cvgP _ (cvgB _ _); apply. Qed.

Lemma is_cvgDlE f g : cvg (g @ F) -> cvg ((f + g) @ F) = cvg (f @ F).
Proof.
move=> g_cvg; rewrite propeqE; split; last by move=> /is_cvgD; apply.
by move=> /is_cvgB /(_ g_cvg); rewrite addrK.
Qed.

Lemma is_cvgDrE f g : cvg (f @ F) -> cvg ((f + g) @ F) = cvg (g @ F).
Proof. by rewrite addrC; apply: is_cvgDlE. Qed.

Lemma cvg_sub0 f g a : (f - g) @ F --> (0 : V) -> g @ F --> a -> f @ F --> a.
Proof.
by move=> Cfg Cg; have := cvgD Cfg Cg; rewrite subrK add0r; apply.
Qed.

Lemma cvg_zero f a : (f - cst a) @ F --> (0 : V) -> f @ F --> a.
Proof. by move=> Cfa; apply: cvg_sub0 Cfa (cvg_cst _). Qed.

Lemma subr_cvg0 f a : (fun x => f x - a) @ F --> 0 <-> f @ F --> a.
Proof.
split=> [?|fFk]; first exact: cvg_zero.
by rewrite -(@subrr _ a)//; apply: cvgB => //; exact: cvg_cst.
Qed.

Lemma cvg_norm f a : f @ F --> a -> `|f x| @[x --> F] --> (`|a| : K).
Proof. by apply: continuous_cvg; apply: norm_continuous. Qed.

Lemma is_cvg_norm f : cvg (f @ F) -> cvg ((Num.norm \o f : T -> K) @ F).
Proof. by have := cvgP _ (cvg_norm _); apply. Qed.

Lemma norm_cvg0P f : `|f x| @[x --> F] --> 0 <-> f @ F --> 0.
Proof.
split; last by move=> /cvg_norm; rewrite normr0.
move=> f0; apply/cvgr0Pnorm_lt => e e_gt0.
by near do rewrite -normr_id; apply: cvgr0_norm_lt.
Unshelve. all: by end_near. Qed.

Lemma norm_cvg0 f : `|f x| @[x --> F] --> 0 -> f @ F --> 0.
Proof. by rewrite norm_cvg0P. Qed.

End cvg_composition_pseudometric.

Lemma cvgr_expr2 {R : realFieldType} : (x ^+ 2 : R) @[x --> +oo] --> +oo.
Proof.
by apply/cvgryPge => M; near=> x; rewrite (@le_trans _ _ x)// expr2 ler_peMl.
Unshelve. all: end_near. Qed.

Lemma cvgr_idn {R : realType} : (n%:R : R) @[n --> \oo] --> +oo.
Proof.
by apply/cvgryPge => M; exact: nbhs_infty_ger.
Unshelve. all: end_near. Qed.

Section cvg_composition_normed.
Context {K : numFieldType} {V : normedModType K} {T : Type}.
Context (F : set_system T) {FF : Filter F}.
Implicit Types (f g : T -> V) (s : T -> K) (k : K) (x : T) (a b : V).

Lemma cvgZ s f k a : s @ F --> k -> f @ F --> a ->
                     s x *: f x @[x --> F] --> k *: a.
Proof. by move=> ? ?; apply: continuous2_cvg => //; apply scale_continuous. Qed.

Lemma is_cvgZ s f : cvg (s @ F) ->
  cvg (f @ F) -> cvg ((fun x => s x *: f x) @ F).
Proof. by have := cvgP _ (cvgZ _ _); apply. Qed.

Lemma cvgZl s k a : s @ F --> k -> s x *: a @[x --> F] --> k *: a.
Proof. by move=> ?; apply: cvgZ => //; exact: cvg_cst. Qed.

Lemma is_cvgZl s a : cvg (s @ F) -> cvg ((fun x => s x *: a) @ F).
Proof. by have := cvgP _ (cvgZl  _); apply. Qed.

Lemma cvgZr k f a : f @ F --> a -> k \*: f @ F --> k *: a.
Proof. apply: cvgZ => //; exact: cvg_cst. Qed.

Lemma is_cvgZr k f : cvg (f @ F) -> cvg (k *: f  @ F).
Proof. by have := cvgP _ (cvgZr  _); apply. Qed.

Lemma is_cvgZrE k f : k != 0 -> cvg (k *: f @ F) = cvg (f @ F).
Proof.
move=> k_neq0; rewrite propeqE; split => [/(@cvgZr k^-1)|/(@cvgZr k)/cvgP//].
by under [_ \*: _]funext => x /= do rewrite scalerK//; apply: cvgP.
Qed.

End cvg_composition_normed.

Section cvg_composition_field.
Context {K : numFieldType}  {T : Type}.
Context (F : set_system T) {FF : Filter F}.
Implicit Types (f g : T -> K) (a b : K).

Lemma cvgV f a : a != 0 -> f @ F --> a -> f\^-1 @ F --> a^-1.
Proof.
by move=> k_neq0 f_cvg; apply: continuous_cvg => //; apply: inv_continuous.
Qed.

Lemma cvgVP f a : a != 0 -> f\^-1 @ F --> a^-1 <-> f @ F --> a.
Proof.
move=> aN0; split=> /(cvgV _); last exact.
by rewrite invrK invr_eq0 inv_funK; apply.
Qed.

Lemma is_cvgV f : lim (f @ F) != 0 -> cvg (f @ F) -> cvg (f\^-1 @ F).
Proof. by move=> /cvgV cvf /cvf /cvgP. Qed.

Lemma cvgM f g a b : f @ F --> a -> g @ F --> b -> (f \* g) @ F --> a * b.
Proof. exact: cvgZ. Qed.

Lemma cvgMl f a b : f @ F --> a -> (f x * b) @[x --> F] --> a * b.
Proof. exact: cvgZl. Qed.

Lemma cvgMr g a b : g @ F --> b -> (a * g x) @[x --> F] --> a * b.
Proof. exact: cvgZr. Qed.

Lemma is_cvgM f g : cvg (f @ F) -> cvg (g @ F) -> cvg (f \* g @ F).
Proof. exact: is_cvgZ. Qed.

Lemma is_cvgMr g a (f := fun=> a) : cvg (g @ F) -> cvg (f \* g @ F).
Proof. exact: is_cvgZr. Qed.

Lemma is_cvgMrE g a (f := fun=> a) : a != 0 -> cvg (f \* g @ F) = cvg (g @ F).
Proof. exact: is_cvgZrE. Qed.

Lemma is_cvgMl f a (g := fun=> a) : cvg (f @ F) -> cvg (f \* g @ F).
Proof.
move=> f_cvg; have -> : f \* g = g \* f by apply/funeqP=> x; rewrite /= mulrC.
exact: is_cvgMr.
Qed.

Lemma is_cvgMlE f a (g := fun=> a) : a != 0 -> cvg (f \* g @ F) = cvg (f @ F).
Proof.
move=> a_neq0; have -> : f \* g = g \* f by apply/funeqP=> x; rewrite /= mulrC.
exact: is_cvgMrE.
Qed.

End cvg_composition_field.

Section limit_composition_pseudometric.

Context {K : numFieldType} {V : pseudoMetricNormedZmodType K} {T : Type}.
Context (F : set_system T) {FF : ProperFilter F}.
Implicit Types (f g : T -> V) (s : T -> K) (k : K) (x : T) (a : V).

Lemma limN f : cvg (f @ F) -> lim (- f @ F) = - lim (f @ F).
Proof. by move=> ?; apply: cvg_lim => //; apply: cvgN. Qed.

Lemma limD f g : cvg (f @ F) -> cvg (g @ F) ->
   lim (f + g @ F) = lim (f @ F) + lim (g @ F).
Proof. by move=> ? ?; apply: cvg_lim => //; apply: cvgD. Qed.

Lemma limB f g : cvg (f @ F) -> cvg (g @ F) ->
   lim (f - g @ F) = lim (f @ F) - lim (g @ F).
Proof. by move=> ? ?; apply: cvg_lim => //; apply: cvgB. Qed.

Lemma lim_norm f : cvg (f @ F) -> lim ((fun x => `|f x| : K) @ F) = `|lim (f @ F)|.
Proof. by move=> ?; apply: cvg_lim => //; apply: cvg_norm. Qed.

End limit_composition_pseudometric.

Section limit_composition_normed.

Context {K : numFieldType} {V : normedModType K} {T : Type}.
Context (F : set_system T) {FF : ProperFilter F}.
Implicit Types (f g : T -> V) (s : T -> K) (k : K) (x : T) (a : V).

Lemma limZ s f : cvg (s @ F) -> cvg (f @ F) ->
   lim ((fun x => s x *: f x) @ F) = lim (s @ F) *: lim (f @ F).
Proof. by move=> ? ?; apply: cvg_lim => //; apply: cvgZ. Qed.

Lemma limZl s a : cvg (s @ F) ->
   lim ((fun x => s x *: a) @ F) = lim (s @ F) *: a.
Proof. by move=> ?; apply: cvg_lim => //; apply: cvgZl. Qed.

Lemma limZr k f : cvg (f @ F) -> lim (k *: f @ F) = k *: lim (f @ F).
Proof. by move=> ?; apply: cvg_lim => //; apply: cvgZr. Qed.

End limit_composition_normed.

Section limit_composition_field.

Context {K : numFieldType} {T : Type}.
Context (F : set_system T) {FF : ProperFilter F}.
Implicit Types (f g : T -> K).

Lemma limM f g : cvg (f @ F) -> cvg (g @ F) ->
   lim (f \* g @ F) = lim (f @ F) * lim (g @ F).
Proof. by move=> ? ?; apply: cvg_lim => //; apply: cvgM. Qed.

End limit_composition_field.

Section cvg_composition_field_proper.

Context {K : numFieldType}  {T : Type}.
Context (F : set_system T) {FF : ProperFilter F}.
Implicit Types (f g : T -> K) (a b : K).

Lemma limV f : lim (f @ F) != 0 -> lim (f\^-1 @ F) = (lim (f @ F))^-1.
Proof.
by move=> ?; apply: cvg_lim => //; apply: cvgV => //; apply: cvgNpoint.
Qed.

Lemma is_cvgVE f : lim (f @ F) != 0 -> cvg (f\^-1 @ F) = cvg (f @ F).
Proof.
move=> ?; apply/propeqP; split=> /is_cvgV; last exact.
by rewrite inv_funK; apply; rewrite limV ?invr_eq0//.
Qed.

End cvg_composition_field_proper.

Section ProperFilterRealType.
Context {T : Type} {F : set_system T} {FF : ProperFilter F} {R : realFieldType}.
Implicit Types (f g h : T -> R) (a b : R).

Lemma cvgr_to_ge f a b : f @ F --> a -> (\near F, b <= f F) -> b <= a.
Proof. by move=> /[swap]/(closed_cvg _ (@closed_ge _ b))/[apply]. Qed.

Lemma cvgr_to_le f a b : f @ F --> a -> (\near F, f F <= b) -> a <= b.
Proof. by move=> /[swap]/(closed_cvg _ (@closed_le _ b))/[apply]. Qed.

Lemma limr_ge x f : cvg (f @ F) -> (\near F, x <= f F) -> x <= lim (f @ F).
Proof. exact: cvgr_to_ge. Qed.

Lemma limr_le x f : cvg (f @ F) -> (\near F, x >= f F) -> x >= lim (f @ F).
Proof. exact: cvgr_to_le. Qed.

End ProperFilterRealType.

Section local_continuity.

Context {K : numFieldType} {V : normedModType K} {T : topologicalType}.
Implicit Types (f g : T -> V) (s t : T -> K) (x : T) (k : K) (a : V).

Lemma continuousN (f : T -> V) x :
  {for x, continuous f} -> {for x, continuous (fun x => - f x)}.
Proof. by move=> ?; apply: cvgN. Qed.

Lemma continuousD f g x :
  {for x, continuous f} -> {for x, continuous g} ->
  {for x, continuous (f + g)}.
Proof. by move=> f_cont g_cont; apply: cvgD. Qed.

Lemma continuousB f g x :
  {for x, continuous f} -> {for x, continuous g} ->
  {for x, continuous (f - g)}.
Proof. by move=> f_cont g_cont; apply: cvgB. Qed.

Lemma continuousZ s f x :
  {for x, continuous s} -> {for x, continuous f} ->
  {for x, continuous (fun x => s x *: f x)}.
Proof. by move=> ? ?; apply: cvgZ. Qed.

Lemma continuousZr f k x :
  {for x, continuous f} -> {for x, continuous (k \*: f)}.
Proof. by move=> ?; apply: cvgZr. Qed.

Lemma continuousZl s a x :
  {for x, continuous s} -> {for x, continuous (fun z => s z *: a)}.
Proof. by move=> ?; apply: cvgZl. Qed.

Lemma continuousM s t x :
  {for x, continuous s} -> {for x, continuous t} ->
  {for x, continuous (s \* t)}.
Proof. by move=> f_cont g_cont; apply: cvgM. Qed.

Lemma continuousV s x : s x != 0 ->
  {for x, continuous s} -> {for x, continuous (fun x => (s x)^-1%R)}.
Proof. by move=> ?; apply: cvgV. Qed.

End local_continuity.

Section nbhs_ereal.
Context {R : numFieldType} (P : \bar R -> Prop).

Lemma nbhs_EFin (x : R) : (\forall y \near x%:E, P y) <-> \near x, P x%:E.
Proof. done. Qed.

Lemma nbhs_ereal_pinfty :
  (\forall x \near +oo%E, P x) <-> [/\ P +oo%E & \forall x \near +oo, P x%:E].
Proof.
split=> [|[Py]] [x [xr Px]]; last by exists x; split=> // -[y||]//; apply: Px.
by split; [|exists x; split=> // y xy]; apply: Px.
Qed.

Lemma nbhs_ereal_ninfty :
  (\forall x \near -oo%E, P x) <-> [/\ P -oo%E & \forall x \near -oo, P x%:E].
Proof.
split=> [|[Py]] [x [xr Px]]; last by exists x; split=> // -[y||]//; apply: Px.
by split; [|exists x; split=> // y xy]; apply: Px.
Qed.
End nbhs_ereal.

Section cvg_fin.
Context {R : numFieldType}.

Section filter.
Context {F : set_system \bar R} {FF : Filter F}.

Lemma fine_fcvg a : F --> a%:E -> fine @ F --> a.
Proof.
move=> /(_ _)/= Fa; apply/cvgrPdist_lt=> // _/posnumP[e]; rewrite near_simpl.
by apply: Fa; apply/nbhs_EFin => /=; apply: (@cvgr_dist_lt _ _ _ (nbhs a)).
(* BUG: using cvgr_dist_lt without (nbhs _) expands the definition of nbhs, *)
(*    so that it is not recognized as a filter anymore *)
Qed.

Lemma fcvg_is_fine a : F --> a%:E -> \near F, F \is a fin_num.
Proof. by apply; apply/nbhs_EFin; near=> x. Unshelve. all: by end_near. Qed.

End filter.

Section limit.
Context {I : Type} {F : set_system I} {FF : Filter F} (f : I -> \bar R).

Lemma fine_cvg a : f @ F --> a%:E -> fine \o f @ F --> a.
Proof. exact: fine_fcvg. Qed.

Lemma cvg_is_fine a : f @ F --> a%:E -> \near F, f F \is a fin_num.
Proof. exact: fcvg_is_fine. Qed.

Lemma cvg_EFin a : (\near F, f F \is a fin_num) -> fine \o f @ F --> a ->
  f @ F --> a%:E.
Proof.
move=> Ffin Fa P/= /nbhs_EFin /Fa; rewrite !near_simpl.
by apply: filterS2 Ffin => x /fineK->.
Qed.

Lemma fine_cvgP a :
   f @ F --> a%:E <-> (\near F, f F \is a fin_num) /\ fine \o f @ F --> a.
Proof.
by split;[split;[exact: (@cvg_is_fine a)|exact: fine_cvg]|case; apply: cvg_EFin].
Qed.

Lemma neq0_fine_cvgP a : a != 0 -> f @ F --> a%:E <-> fine \o f @ F --> a.
Proof.
move=> a_neq0; split=> [|Fa]; first exact: fine_cvg.
apply: cvg_EFin=> //; near (0 : R)^'+ => e.
have lea : e <= `|a| by near: e; apply: nbhs_right_le; rewrite normr_gt0.
near=> x; have : `|a - fine (f x)| < e by near: x; apply: cvgr_dist_lt.
by case: f=> //=; rewrite subr0; apply: contra_ltT.
Unshelve. all: by end_near. Qed.

End limit.

End cvg_fin.

Section ecvg_realFieldType.
Context {I} {F : set_system I} {FF : Filter F} {R : realFieldType}.
Implicit Types f g u v : I -> \bar R.
Local Open Scope ereal_scope.

Lemma cvgeD f g a b :
  a +? b -> f @ F --> a -> g @ F --> b -> f \+ g @ F --> a + b.
Proof.
have yE u v x : u @ F --> +oo -> v @ F --> x%:E -> u \+ v @ F --> +oo.
  move=> /cvgeyPge/= foo /fine_cvgP[Fg gb]; apply/cvgeyPgey.
  near=> A; near=> n; have /(_ _)/wrap[//|Fgn] := near Fg n.
  rewrite -leeBlDr// (@le_trans _ _ (A - (x - 1))%:E)//; last by near: n.
  rewrite ?EFinB leeB// leeBlDr// -[v n]fineK// -EFinD lee_fin.
  by rewrite ler_distlDr// ltW//; near: n; apply: cvgr_dist_lt.
have NyE u v x : u @ F --> -oo -> v @ F --> x%:E -> u \+ v @ F --> -oo.
  move=> /cvgeNyPle/= foo /fine_cvgP -[Fg gb]; apply/cvgeNyPleNy.
  near=> A; near=> n; have /(_ _)/wrap[//|Fgn] := near Fg n.
  rewrite -leeBrDr// (@le_trans _ _ (A - (x + 1))%:E)//; first by near: n.
  rewrite ?EFinB ?EFinD leeB// -[v n]fineK// -EFinD lee_fin.
  by rewrite ler_distlCDr// ltW//; near: n; apply: cvgr_dist_lt.
have yyE u v : u @ F --> +oo -> v @ F --> +oo -> u \+ v @ F --> +oo.
  move=> /cvgeyPge foo /cvgeyPge goo; apply/cvgeyPge => A; near=> y.
  by rewrite -[leLHS]adde0 leeD//; near: y; [apply: foo|apply: goo].
have NyNyE u v : u @ F --> -oo -> v @ F --> -oo -> u \+ v @ F --> -oo.
  move=> /cvgeNyPle foo /cvgeNyPle goo; apply/cvgeNyPle => A; near=> y.
  by rewrite -[leRHS]adde0 leeD//; near: y; [apply: foo|apply: goo].
have addfC u v : u \+ v = v \+ u.
  by apply/funeqP => x; rewrite /= addeC.
move: a b => [a| |] [b| |] //= _; rewrite ?(addey, addye, addeNy, addNye)//=;
  do ?by [apply: yE|apply: NyE|apply: yyE|apply: NyNyE].
- move=> /fine_cvgP[Ff fa] /fine_cvgP[Fg ga]; rewrite -EFinD.
  apply/fine_cvgP; split.
    by near do [rewrite fin_numD; apply/andP; split].
  apply: (@cvg_trans _ ((fine \o f) \+ (fine \o g) @ F))%R; last exact: cvgD.
  by apply: near_eq_cvg; near do rewrite /= fineD//.
- by move=> /[swap]; rewrite addfC; apply: yE.
- by move=> /[swap]; rewrite addfC; apply: NyE.
Unshelve. all: by end_near. Qed.

Lemma cvgeN f x : f @ F --> x -> - f x @[x --> F] --> - x.
Proof. by move=> ?; apply: continuous_cvg => //; exact: oppe_continuous. Qed.

Lemma cvgeNP f a : - f x @[x --> F] --> - a <-> f @ F --> a.
Proof.
by split=> /cvgeN//; rewrite oppeK//; under eq_cvg do rewrite /= oppeK.
Qed.

Lemma cvgeB f g a b :
  a +? - b -> f @ F --> a -> g @ F --> b -> f \- g @ F --> a - b.
Proof. by move=> ab fa gb; apply: cvgeD => //; exact: cvgeN. Qed.

Lemma sube_cvg0 f (k : \bar R) :
  k \is a fin_num -> (fun x => f x - k) @ F --> 0 <-> f @ F --> k.
Proof.
move=> kfin; split.
  move=> /cvgeD-/(_ (cst k) _ isT (cvg_cst _)).
  by rewrite add0e; under eq_fun => x do rewrite subeK//.
move: k kfin => [k _ fk| |]//; rewrite -(@subee _ k%:E)//.
by apply: cvgeB => //; exact: cvg_cst.
Qed.

Lemma abse_continuous : continuous (@abse R).
Proof.
case=> [r|A /= [r [rreal rA]]|A /= [r [rreal rA]]]/=.
- exact/(cvg_comp (@norm_continuous _ R r)).
- by exists r; split => // y ry; apply: rA; rewrite (lt_le_trans ry)// lee_abs.
- exists (- r)%R; rewrite realN; split => // y; rewrite EFinN -lteNr => yr.
  by apply: rA; rewrite (lt_le_trans yr)// -abseN lee_abs.
Qed.

Lemma cvg_abse f (a : \bar R) : f @ F --> a -> `|f x|%E @[x --> F] --> `|a|%E.
Proof. by apply: continuous_cvg => //; apply: abse_continuous. Qed.

Lemma is_cvg_abse (f : I -> \bar R) : cvg (f @ F) -> cvg (`|f x|%E @[x --> F]).
Proof. by move/cvg_abse/cvgP. Qed.

Lemma is_cvgeN f : cvg (f @ F) -> cvg (\- f @ F).
Proof. by move=> /cvg_ex[l fl]; apply: (cvgP (- l)); exact: cvgeN. Qed.

Lemma is_cvgeNE f : cvg (\- f @ F) = cvg (f @ F).
Proof.
rewrite propeqE; split=> /cvgeNP/cvgP//.
by under eq_is_cvg do rewrite oppeK.
Qed.

Lemma mule_continuous (r : R) : continuous (mule r%:E).
Proof.
rewrite /continuous_at; wlog r0 : r / (r > 0)%R => [hwlog|].
  have [r0|r0|->] := ltrgtP r 0; do ?exact: hwlog; last first.
    by move=> x; rewrite mul0e; apply: cvg_near_cst; near=> y; rewrite mul0e.
  have -> : *%E r%:E = \- ( *%E (- r)%:E ).
    by apply/funeqP=> x /=; rewrite EFinN mulNe oppeK.
  move=> x; apply: (continuous_comp (hwlog (- r)%R _ _)); rewrite ?oppr_gt0//.
  exact: oppe_continuous.
move=> [s||]/=.
- rewrite -EFinM; apply: cvg_EFin => /=.
    by apply/nbhs_EFin; near do rewrite fin_numM//.
  move=> P /= Prs; apply/nbhs_EFin=> //=.
  by apply: near_fun => //=; apply: continuousM => //=; apply: cvg_cst.
- rewrite gt0_muley ?lte_fin// => A [u [realu uA]].
  exists (r^-1 * u)%R; split; first by rewrite realM// realV realE ltW.
  by move=> x rux; apply: uA; move: rux; rewrite EFinM lte_pdivrMl.
- rewrite gt0_muleNy ?lte_fin// => A [u [realu uA]].
  exists (r^-1 * u)%R; split; first by rewrite realM// realV realE ltW.
  by move=> x xru; apply: uA; move: xru; rewrite EFinM lte_pdivlMl.
Unshelve. all: by end_near. Qed.

Lemma cvgeMl f x y : y \is a fin_num ->
  f @ F --> x -> (fun n => y * f n) @ F --> y * x.
Proof. by move: y => [r| |]// _ /cvg_comp; apply; exact: mule_continuous. Qed.

Lemma is_cvgeMl f y : y \is a fin_num ->
  cvg (f @ F) -> cvg ((fun n => y * f n) @ F).
Proof. by move=> fy /(cvgeMl fy)/cvgP. Qed.

Lemma cvgeMr f x y : y \is a fin_num ->
  f @ F --> x -> (fun n => f n * y) @ F --> x * y.
Proof.
by move=> ? ?; rewrite muleC; under eq_fun do rewrite muleC; exact: cvgeMl.
Qed.

Lemma is_cvgeMr f y : y \is a fin_num ->
  cvg (f @ F) -> cvg ((fun n => f n * y) @ F).
Proof. by move=> fy /(cvgeMr fy)/cvgP. Qed.

Lemma cvg_abse0P f : abse \o f @ F --> 0 <-> f @ F --> 0.
Proof.
split; last by move=> /cvg_abse; rewrite abse0.
move=> /cvg_ballP f0; apply/cvg_ballP => _/posnumP[e].
have := [elaborate f0 _ (gt0 e)].
rewrite !near_simpl => absf0; rewrite near_simpl.
apply: filterS absf0 => x /=; rewrite /ball/= /ereal_ball !contract0 !sub0r !normrN.
have [fx0|fx0] := leP 0 (f x); first by rewrite gee0_abs.
by rewrite (lte0_abs fx0) contractN normrN.
Qed.

Let cvgeM_gt0_pinfty f g b :
  (0 < b)%R -> f @ F --> +oo -> g @ F --> b%:E -> f \* g @ F --> +oo.
Proof.
move=> b_gt0 /cvgeyPge foo /fine_cvgP[gfin gb]; apply/cvgeyPgey.
near (0%R : R)^'+ => e; near=> A; near=> n.
rewrite (@le_trans _ _ (f n * e%:E))// ?lee_pmul// ?lee_fin//.
- by rewrite -lee_pdivrMr ?divr_gt0//; near: n; apply: foo.
- by rewrite (@le_trans _ _ 1) ?lee_fin//; near: n; apply: foo.
rewrite -(@fineK _ (g n)) ?lee_fin; last by near: n; exact: gfin.
by near: n; apply: (cvgr_ge b).
Unshelve. all: end_near. Qed.

Let cvgeM_lt0_pinfty  f g b :
  (b < 0)%R -> f @ F --> +oo -> g @ F --> b%:E -> f \* g @ F --> -oo.
Proof.
move=> b0 /cvgeyPge foo /fine_cvgP -[gfin gb]; apply/cvgeNyPleNy.
near (0%R : R)^'+ => e; near=> A; near=> n.
rewrite -leeN2 -muleN (@le_trans _ _ (f n * e%:E))//.
  by rewrite -lee_pdivrMr ?mulr_gt0 ?oppr_gt0//; near: n; apply: foo.
rewrite lee_pmul ?lee_fin//.
  by rewrite (@le_trans _ _ 1) ?lee_fin//; near: n; apply: foo.
rewrite -(@fineK _ (g n)) ?lee_fin; last by near: n; exact: gfin.
near: n; apply: (cvgr_ge (- b)); rewrite 1?cvgNP//.
by near: e; apply: nbhs_right_lt; rewrite oppr_gt0.
Unshelve. all: end_near. Qed.

Let cvgeM_gt0_ninfty f g b :
  (0 < b)%R -> f @ F --> -oo -> g @ F --> b%:E -> f \* g @ F --> -oo.
Proof.
move=> b0 foo gb; under eq_fun do rewrite -muleNN.
apply: (@cvgeM_lt0_pinfty _ _ (- b)%R); first by rewrite oppr_lt0.
- by rewrite -(oppeK +oo); apply: cvgeN.
- by rewrite EFinN; apply: cvgeN.
Qed.

Let cvgeM_lt0_ninfty f g b :
  (b < 0)%R -> f @ F --> -oo -> g @ F --> b%:E -> f \* g @ F --> +oo.
Proof.
move=> b0 foo gb; under eq_fun do rewrite -muleNN.
apply: (@cvgeM_gt0_pinfty _ _ (- b)%R); first by rewrite oppr_gt0.
- by rewrite -(oppeK +oo); apply: cvgeN.
- by rewrite EFinN; apply: cvgeN.
Qed.

Lemma cvgeM f g (a b : \bar R) :
 a *? b -> f @ F --> a -> g @ F --> b -> f \* g @ F --> a * b.
Proof.
move=> [:apoo] [:bnoo] [:poopoo] [:poonoo]; move: a b => [a| |] [b| |] //.
- move=> _ /fine_cvgP[finf fa] /fine_cvgP[fing gb].
  apply/fine_cvgP; split.
    by near do apply: fin_numM; [apply: finf | apply: fing].
  apply: (@cvg_trans _ (((fine \o f) \* (fine \o g)) @ F)%R).
    apply: near_eq_cvg; near=> n => //=.
    rewrite -[in RHS](@fineK _ (f n)); last by near: n; exact: finf.
    by rewrite -[in RHS](@fineK _ (g n)) //; near: n; exact: fing.
  exact: cvgM.
- move: f g a; abstract: apoo.
  move=> {}f {}g {}a + fa goo; have [a0 _|a0 _|->] := ltgtP a 0%R.
  + rewrite mulry ltr0_sg// ?mulN1e.
    by under eq_fun do rewrite muleC; exact: (cvgeM_lt0_pinfty a0).
  + rewrite mulry gtr0_sg// ?mul1e.
    by under eq_fun do rewrite muleC; exact: (cvgeM_gt0_pinfty a0).
  + by rewrite /mule_def eqxx.
- move: f g a; abstract: bnoo.
  move=> {}f {}g {}a + fa goo; have [a0 _|a0 _|->] := ltgtP a 0%R.
  + rewrite mulrNy ltr0_sg// ?mulN1e.
    by under eq_fun do rewrite muleC; exact: (cvgeM_lt0_ninfty a0).
  + rewrite mulrNy gtr0_sg// ?mul1e.
    by under eq_fun do rewrite muleC; exact: (cvgeM_gt0_ninfty a0).
  + by rewrite /mule_def eqxx.
- rewrite mule_defC => ? foo gb; rewrite muleC.
  by under eq_fun do rewrite muleC; exact: apoo.
- move=> _; move: f g; abstract: poopoo.
  move=> {}f {}g /cvgeyPge foo /cvgeyPge goo.
  rewrite mulyy; apply/cvgeyPgey; near=> A; near=> n.
  have A_gt0 : (0 <= A)%R by [].
  by rewrite -[leLHS]mule1 lee_pmul//=; near: n; [apply: foo|apply: goo].
- move=> _; move: f g; abstract: poonoo.
  move=> {}f {}g /cvgeyPge foo /cvgeNyPle goo.
  rewrite mulyNy; apply/cvgeNyPle => A; near=> n.
  rewrite (@le_trans _ _ (g n))//; last by near: n; exact: goo.
  apply: lee_nemull; last by near: n; apply: foo.
  by rewrite (@le_trans _ _ (- 1)%:E)//; near: n; apply: goo; rewrite ltrN10.
- rewrite mule_defC => ? foo gb; rewrite muleC.
  by under eq_fun do rewrite muleC; exact: bnoo.
- move=> _ foo goo.
  by under eq_fun do rewrite muleC; exact: poonoo.
- move=> _ foo goo; rewrite mulNyNy -mulyy.
  by under eq_fun do rewrite -muleNN; apply: poopoo;
    rewrite -/(- -oo); apply: cvgeN.
Unshelve. all: end_near. Qed.

End ecvg_realFieldType.
#[deprecated(since="mathcomp-analysis 1.9.0", note="renamed to `sube_cvg0`")]
Notation cvge_sub0 := sube_cvg0 (only parsing).

Section max_cts.
Context {R : realType} {T : topologicalType}.

Lemma continuous_min (f g : T -> R^o) x :
  {for x, continuous f} -> {for x, continuous g} ->
  {for x, continuous (f \min g)}.
Proof.
move=> ctsf ctsg.
under [_ \min _]eq_fun => ? do rewrite minr_absE.
apply: cvgM; [|exact: cvg_cst]; apply:cvgD; first exact: cvgD.
by apply: cvgN; apply: cvg_norm; apply: cvgB.
Qed.

Lemma continuous_max (f g : T -> R^o) x :
  {for x, continuous f} -> {for x, continuous g} ->
  {for x, continuous (f \max g)}.
Proof.
move=> ctsf ctsg.
under [_ \max _]eq_fun => ? do rewrite maxr_absE.
apply: cvgM; [|exact: cvg_cst]; apply:cvgD; first exact: cvgD.
by apply: cvg_norm; apply: cvgB.
Qed.

End max_cts.

Section pseudoMetricDist.
Context {R : realType} {X : pseudoMetricType R}.
Implicit Types r : R.

Definition edist (xy : X * X) : \bar R :=
  ereal_inf (EFin @` [set r | 0 < r /\ ball xy.1 r xy.2]).

Lemma edist_ge0 (xy : X * X) : (0 <= edist xy)%E.
Proof.
by apply: lb_ereal_inf => z [+ []] => _/posnumP[r] _ <-; rewrite lee_fin.
Qed.
Hint Resolve edist_ge0 : core.

Lemma edist_neqNy (xy : X * X) : (edist xy != -oo)%E.
Proof. by rewrite -lteNye (@lt_le_trans _ _ 0%E). Qed.
Hint Resolve edist_neqNy : core.

Lemma edist_lt_ball r (xy : X * X) : (edist xy < r%:E)%E -> ball xy.1 r xy.2.
Proof.
case/ereal_inf_lt => ? [+ []] => _/posnumP[eps] bxye <-; rewrite lte_fin.
by move/ltW/le_ball; exact.
Qed.

Lemma edist_fin r (xy : X * X) :
  0 < r -> ball xy.1 r xy.2 -> (edist xy <= r%:E)%E.
Proof.
move: r => _/posnumP[r] => ?; rewrite -(ereal_inf1 r%:num%:E) le_ereal_inf //.
by move=> ? -> /=; exists r%:num; split.
Qed.

Lemma edist_pinftyP (xy : X * X) :
  (edist xy = +oo)%E <-> (forall r, 0 < r -> ~ ball xy.1 r xy.2).
Proof.
split.
  move/ereal_inf_pinfty => xrb r rpos rb; move: (ltry r); rewrite ltey => /eqP.
  by apply; apply: xrb; exists r.
rewrite /edist=> nrb; suff -> : [set r | 0 < r /\ ball xy.1 r xy.2] = set0.
  by rewrite image_set0 ereal_inf0.
by rewrite -subset0 => r [?] rb; apply: nrb; last exact: rb.
Qed.

Lemma edist_finP (xy : X * X) :
  (edist xy \is a fin_num)%E <-> exists2 r, 0 < r & ball xy.1 r xy.2.
Proof.
rewrite ge0_fin_numE ?edist_ge0// ltey.
rewrite -(rwP (negPP eqP)); apply/iff_not2; rewrite notE.
apply: (iff_trans (edist_pinftyP _)); apply: (iff_trans _ (forall2NP _ _)).
by under eq_forall => ? do rewrite implyE.
Qed.

Lemma edist_fin_open : open [set xy : X * X | edist xy \is a fin_num].
Proof.
move=> z /= /edist_finP [] _/posnumP[r] bzr.
exists (ball z.1 r%:num, ball z.2 r%:num); first by split; exact: nbhsx_ballx.
case=> a b [bza bzb]; apply/edist_finP; exists (r%:num + r%:num + r%:num) => //.
exact/(ball_triangle _ bzb)/(ball_triangle _ bzr)/ball_sym.
Qed.

Lemma edist_fin_closed : closed [set xy : X * X | edist xy \is a fin_num].
Proof.
move=> z /= /(_ (ball z 1)) []; first exact: nbhsx_ballx.
move=> w [/edist_finP [] _/posnumP[r] babr [bz1w1 bz2w2]]; apply/edist_finP.
exists (1 + (r%:num + 1)) => //.
exact/(ball_triangle bz1w1)/(ball_triangle babr)/ball_sym.
Qed.

Lemma edist_pinfty_open : open [set xy : X * X | edist xy = +oo]%E.
Proof.
rewrite -closedC; have := edist_fin_closed; congr (_ _).
by rewrite eqEsubset; split => z; rewrite /= ?ge0_fin_numE// ltey => /eqP.
Qed.

Lemma edist_sym (x y : X) : edist (x, y) = edist (y, x).
Proof. by rewrite /edist /=; under eq_fun do rewrite ball_symE. Qed.

Lemma edist_triangle (x y z : X) :
  (edist (x, z) <= edist (x, y) + edist (y, z))%E.
Proof.
have [->|] := eqVneq (edist (x, y)) +oo%E; first by rewrite addye ?leey.
have [->|] := eqVneq (edist (y, z)) +oo%E; first by rewrite addey ?leey.
rewrite -?ltey -?ge0_fin_numE//.
move=> /edist_finP [_/posnumP[r2] /= yz] /edist_finP [_/posnumP[r1] /= xy].
have [|] := eqVneq (edist (x, z)) +oo%E.
  move/edist_pinftyP /(_ (r1%:num + r2%:num) _) => -[//|].
  exact: (ball_triangle xy).
rewrite -ltey -ge0_fin_numE// => /[dup] xzfin.
move/edist_finP => [_/posnumP[del] /= xz].
rewrite /edist /= ?ereal_inf_EFin; first last.
- by exists (r1%:num + r2%:num); split => //; apply: (ball_triangle xy).
- by exists 0 => ? /= [/ltW].
- by exists r1%:num; split.
- by exists 0 => ? /= [/ltW].
- by exists r2%:num; split.
- by exists 0 => ? /= [/ltW].
rewrite -EFinD lee_fin -inf_sumE //; first last.
- by split; [exists r2%:num; split| exists 0 => ? /= [/ltW]].
- by split; [exists r1%:num; split| exists 0 => ? /= [/ltW]].
apply: lb_le_inf.
  by exists (r1%:num + r2%:num); exists r1%:num => //; exists r2%:num.
move=> ? [+ []] => _/posnumP[p] xpy [+ []] => _/posnumP[q] yqz <-.
apply: inf_lbound; first by exists 0 => ? /= [/ltW].
by split => //; exact: (ball_triangle xpy).
Qed.

Lemma edist_continuous : continuous edist.
Proof.
move=> [x y]; have [pE U /= Upinf|] := eqVneq (edist (x, y)) +oo%E.
  rewrite nbhs_simpl /=; apply (@filterS _ _ _ [set xy | edist xy = +oo]%E).
    by move=> z /= ->; apply: nbhs_singleton; move: pE Upinf => ->.
  by apply: open_nbhs_nbhs; split => //; exact: edist_pinfty_open.
rewrite -ltey -ge0_fin_numE// => efin.
rewrite /continuous_at -[edist (x, y)]fineK//; apply: cvg_EFin.
  by have := edist_fin_open efin; apply: filter_app; near=> w.
apply/cvgrPdist_le => _/posnumP[eps].
suff: \forall t \near (nbhs x, nbhs y),
   `|fine (edist (x, y)) - fine (edist t)| <= eps%:num by [].
rewrite -near2_pair; near=> a b => /=.
have abxy : (edist (a, b) <= edist (x, a) + edist (x, y) + edist (y, b))%E.
  rewrite (edist_sym x a) -addeA.
  by rewrite (le_trans (@edist_triangle _ x _)) ?leeD ?edist_triangle.
have xyab : (edist (x, y) <= edist (x, a) + edist (a, b) + edist (y, b))%E.
  rewrite (edist_sym y b) -addeA.
  by rewrite (le_trans (@edist_triangle _ a _))// ?leeD// ?edist_triangle.
have xafin : edist (x, a) \is a fin_num.
  by apply/edist_finP; exists 1 =>//; near: a; exact: nbhsx_ballx.
have ybfin : edist (y, b) \is a fin_num.
  by apply/edist_finP; exists 1 =>//; near: b; exact: nbhsx_ballx.
have abfin : edist (a, b) \is a fin_num.
  by rewrite ge0_fin_numE// (le_lt_trans abxy) ?lte_add_pinfty// -ge0_fin_numE.
have xyabfin : (edist (x, y) - edist (a, b))%E \is a fin_num
  by rewrite fin_numB abfin efin.
rewrite -fineB// -fine_abse// -lee_fin fineK ?abse_fin_num//.
rewrite (@le_trans _ _ (edist (x, a) + edist (y, b))%E)//; last first.
  by rewrite [eps%:num]splitr/= EFinD leeD//; apply: edist_fin => //=;
       [near: a | near: b]; exact: nbhsx_ballx.
have [ab_le_xy|/ltW xy_le_ab] := leP (edist (a, b)) (edist (x, y)).
  by rewrite gee0_abs ?subre_ge0// leeBlDr// addeAC.
rewrite lee0_abs ?sube_le0// oppeB ?fin_num_adde_defr//.
by rewrite addeC leeBlDr// addeAC.
Unshelve. all: end_near. Qed.

Lemma edist_closeP x y : close x y <-> edist (x, y) = 0%E.
Proof.
rewrite ball_close; split=> [bxy|edist0 eps]; first last.
  by apply: (@edist_lt_ball _ (x, y)); rewrite edist0.
case: ltgtP (edist_ge0 (x, y)) => // dpos _.
have xxfin : edist (x, y) \is a fin_num.
  rewrite ge0_fin_numE// (@le_lt_trans _ _ 1%:E) ?ltey// edist_fin//.
  exact: bxy (widen_itv 1%:itv).
have dpose : fine (edist (x, y)) > 0 by rewrite -lte_fin fineK.
pose eps := PosNum dpose.
have : (edist (x, y) <= (eps%:num / 2)%:E)%E.
  apply: ereal_inf_lbound; exists (eps%:num / 2) => //; split => //.
  exact: (bxy (eps%:num / 2)%:pos).
apply: contra_leP => _.
by rewrite /= EFinM fineK// lte_pdivrMr// lte_pmulr// lte1n.
Qed.

Lemma edist_refl x : edist (x, x) = 0%E. Proof. exact/edist_closeP. Qed.

Lemma edist_closel x y z : close x y -> edist (x, z) = edist (y, z).
Proof.
move=> /edist_closeP xy0; apply: le_anti; apply/andP; split.
  by rewrite -[edist (y, z)]add0e -xy0 edist_triangle.
by rewrite -[edist (x, z)]add0e -xy0 [edist (x, y)]edist_sym edist_triangle.
Qed.

End pseudoMetricDist.
#[global]
Hint Extern 0 (is_true (0%R <= edist _)%E) => solve [apply: edist_ge0] : core.
#[global]
Hint Extern 0 (is_true (edist _ != -oo%E)) => solve [apply: edist_neqNy] : core.

Section edist_inf.
Context {R : realType} {T : pseudoMetricType R} (A : set T).

Definition edist_inf z := ereal_inf [set edist (z, a) | a in A].

Lemma edist_inf_ge0 w : (0 <= edist_inf w)%E.
Proof. by apply: lb_ereal_inf => ? /= [? ? <-]. Qed.
Hint Resolve edist_inf_ge0 : core.

Lemma edist_inf_neqNy w : (edist_inf w != -oo)%E.
Proof. by rewrite -lteNye (@lt_le_trans _ _ 0%E). Qed.
Hint Resolve edist_inf_neqNy : core.

Lemma edist_inf_triangle x y : (edist_inf x <= edist (x, y) + edist_inf y)%E.
Proof.
have [A0|/set0P[a0 Aa0]] := eqVneq A set0.
  by rewrite /edist_inf A0 ?image_set0 ?ereal_inf0 addey.
have [fyn|] := boolP (edist_inf y \is a fin_num); first last.
  by rewrite ge0_fin_numE// ?ltey negbK => /eqP->; rewrite addey ?leey.
have [xyfin|] := boolP (edist (x, y) \is a fin_num); first last.
  by rewrite ge0_fin_numE// ?ltey // negbK => /eqP->; rewrite addye ?leey.
apply/lee_addgt0Pr => _/posnumP[eps].
have [//|? [a Aa <-] yaeps] := @lb_ereal_inf_adherent R _ eps%:num _ fyn.
apply: le_trans.
  by apply: (@ereal_inf_lbound _ _ (edist (x, a))); exists a.
apply: le_trans; first exact: (@edist_triangle _ _ _ y).
by rewrite -addeA leeD2lE // ltW.
Qed.

Lemma edist_inf_continuous : continuous edist_inf.
Proof.
move=> z; have [A0|/= /set0P[a0 Aa0]] := eqVneq A set0.
  rewrite /edist_inf A0.
  under eq_fun do rewrite image_set0 ereal_inf0.
  exact: cvg_cst.
have [] := eqVneq (edist_inf z) +oo%E.
  move=> /[dup] fzp /ereal_inf_pinfty => zAp U /= Ufz.
  have : nbhs z (ball z 1) by exact: nbhsx_ballx.
  apply: filter_app; near_simpl; near=> w => bz1w.
  suff /= -> : (edist_inf w) = +oo%E by apply: nbhs_singleton; rewrite -fzp.
  apply/ereal_inf_pinfty => r [a Aa] war; apply/zAp; exists a => //.
  have /gee0P[|[r' r'pos war']] := edist_ge0 (w, a).
    by rewrite war => ->; apply: zAp; exists a.
  have := @edist_triangle _ _ z w a; rewrite war'; apply: contra_leP => _.
  rewrite (@le_lt_trans _ _ (1 + r'%:E)%E) ?leeD2r ?edist_fin//.
  by rewrite -EFinD [edist (z, a)]zAp ?ltey //; exists a.
rewrite -ltey -ge0_fin_numE ?edist_inf_ge0 // => fz_fin.
rewrite /continuous_at -[edist_inf z]fineK //; apply/fine_cvgP.
have fwfin : \forall w \near z, edist_inf w \is a fin_num.
  (have : nbhs z (ball z 1) by exact: nbhsx_ballx); apply: filter_app.
  near=> t => bz1; rewrite ge0_fin_numE ?edist_inf_ge0 //.
  rewrite (le_lt_trans (edist_inf_triangle _ z))//.
  rewrite -ge0_fin_numE ?adde_ge0 ?edist_inf_ge0 //.
  rewrite fin_numD fz_fin andbT; apply/edist_finP; exists 1 => //.
  exact/ball_sym.
split => //; apply/cvgrPdist_le => _/posnumP[eps].
have : nbhs z (ball z eps%:num) by exact: nbhsx_ballx.
apply: filter_app; near_simpl; move: fwfin; apply: filter_app.
near=> t => tfin /= /[dup] ?.
have ztfin : edist (z, t) \is a fin_num by apply/edist_finP; exists eps%:num.
move=> /(@edist_fin _ _ _ (z, t)) - /(_ trivial).
rewrite -[edist (z, t)]fineK ?lee_fin //; apply: le_trans.
rewrite ler_norml; apply/andP; split.
  rewrite lerBrDr addrC lerBlDr  addrC -fineD //.
  rewrite -lee_fin ?fineK // ?fin_numD ?ztfin ?fz_fin // edist_sym.
  exact: edist_inf_triangle.
rewrite lerBlDr -fineD // -lee_fin ?fineK // ?fin_numD ?tfin ?ztfin //.
exact: edist_inf_triangle.
Unshelve. all: by end_near. Qed.

Lemma edist_inf0 a : A a -> edist_inf a = 0%E.
Proof.
move=> Aa; apply: le_anti; apply/andP; split; last exact: edist_inf_ge0.
by apply: ereal_inf_lbound; exists a => //; exact: edist_refl.
Qed.

End edist_inf.
#[global]
Hint Extern 0 (is_true (0 <= edist_inf _ _)%E) =>
  solve [apply: edist_inf_ge0] : core.
#[global]
Hint Extern 0 (is_true (edist_inf _ _ != -oo%E)) =>
  solve [apply: edist_inf_neqNy] : core.

Section urysohn_separator.
Context {T : uniformType} {R : realType}.
Context (A B : set T) (E : set (T * T)).
Hypothesis entE : entourage E.
Hypothesis AB0 : A `*` B `&` E = set0.

Local Notation T' := [the pseudoMetricType R of gauge.type entE].

Local Lemma urysohn_separation : exists (f : T -> R),
  [/\ continuous f, range f `<=` `[0, 1],
      f @` A `<=` [set 0] & f @` B `<=` [set 1] ].
Proof.
have [eps exy] : exists (eps : {posnum R}),
    forall (x y : T'), A x -> B y -> ~ ball x eps%:num y.
  have : @entourage T' E by exists O => /=.
  rewrite -entourage_ballE; case=> _/posnumP[eps] epsdiv; exists eps.
  move=> x y Ax By bxy; have divxy := epsdiv (x, y) bxy.
  by have : set0 (x, y) by rewrite -AB0; split.
have [->|/set0P[a A0]] := eqVneq A set0.
  exists (fun=> 1); split; first by move => ?; exact: cvg_cst.
  - by move=> ? [? _ <-]; rewrite /= in_itv /=; apply/andP; split => //.
  - by rewrite image_set0.
  - by move=> ? [? ? <-].
have dfin x : @edist_inf R T' A x \is a fin_num.
  rewrite ge0_fin_numE ?edist_inf_ge0 //; apply: le_lt_trans.
    by apply: ereal_inf_lbound; exists a.
  rewrite -ge0_fin_numE ?edist_ge0 //; apply/edist_finP => /=; exists 2 => //.
  exact: countable_uniform.countable_uniform_bounded.
pose f' := (fun z => fine (@edist_inf R T' A z)) \min (fun=> eps%:num).
pose f z := (f' z)/eps%:num; exists f; split.
- move=> x; rewrite /f; apply: (@cvgM R T (nbhs x)); last exact: cvg_cst.
  suff : {for x, continuous (f' : T' -> R)}.
    move=> Q U; rewrite nbhs_simpl /= => f'U.
    have [J /(gauge.gauge_ent entE) entJ/filterS] := Q _ f'U; apply.
    by rewrite nbhs_simpl /= -nbhs_entourageE /=; exists J.
  apply: continuous_min; last by apply: cvg_cst; exact: nbhs_filter.
  apply: fine_cvg; first exact: nbhs_filter.
  rewrite fineK //; first exact: edist_inf_continuous.
- move=> _ [x _ <-]; rewrite set_itvE /=; apply/andP; split.
    by rewrite /f divr_ge0 // /f' /= le_min fine_ge0//= edist_inf_ge0.
  by rewrite /f ler_pdivrMr // mul1r /f' /= /minr; case: ltP => // /ltW.
- by move=> ? [z Az] <-; rewrite /f/f' /= edist_inf0 // /minr fine0 ifT ?mul0r.
- move=> ? [b Bb] <-; rewrite /f /f'/= /minr/=.
  case: ltP => //; rewrite ?divrr // ?unitf_gt0 // -lte_fin fineK//.
  move => /ereal_inf_lt [_ [z Az <-]] ebz; have [] := exy _ _ Az Bb.
  exact/ball_sym/(@edist_lt_ball R T' _ (b, z)).
Qed.

End urysohn_separator.

Section topological_urysohn_separator.
Context {T : topologicalType} {R : realType}.

Definition uniform_separator (A B : set T) :=
  exists (uT : @Uniform.axioms_ T^o) (E : set (T * T)),
    let UT := Uniform.Pack uT in [/\
      @entourage UT E, A `*` B `&` E = set0 &
      (forall x, @nbhs UT UT x `<=` @nbhs T T x)].

Local Lemma Urysohn' (A B : set T) : exists (f : T -> R),
    [/\ continuous f,
    range f `<=` `[0, 1]
    & uniform_separator A B ->
    f @` A `<=` [set 0] /\ f @` B `<=` [set 1]].
Proof.
have [[? [E [entE ABE0 coarseT]]]|nP] := pselect (uniform_separator A B).
  have [f] := @urysohn_separation _ R _ _ _ entE ABE0.
  by case=> ctsf ? ? ?; exists f; split => // ? ? /= ?; apply/coarseT/ctsf.
exists (fun=>1); split => //; first by move=> ?; exact: cvg_cst.
by move=> ? [? _ <-]; rewrite /= in_itv /=; apply/andP; split => //.
Qed.

Definition Urysohn (A B : set T) : T -> R := projT1 (cid (Urysohn' A B)).

Section urysohn_facts.

Lemma Urysohn_continuous (A B : set T) : continuous (Urysohn A B).
Proof. by have [] := projT2 (cid (@Urysohn' A B)). Qed.

Lemma Urysohn_range (A B : set T) : range (Urysohn A B) `<=` `[0, 1].
Proof. by have [] := projT2 (cid (@Urysohn' A B)). Qed.

Lemma Urysohn_sub0 (A B : set T) :
  uniform_separator A B -> Urysohn A B @` A `<=` [set 0].
Proof. by move=> eE; have [_ _ /(_ eE)[]] := projT2 (cid (@Urysohn' A B)). Qed.

Lemma Urysohn_sub1 (A B : set T) :
  uniform_separator A B -> Urysohn A B @` B `<=` [set 1].
Proof. by move=> eE; have [_ _ /(_ eE)[]] := projT2 (cid (@Urysohn' A B)). Qed.

Lemma Urysohn_eq0 (A B : set T) :
  uniform_separator A B -> A !=set0 -> Urysohn A B @` A = [set 0].
Proof.
move=> eE Aa; have [_ _ /(_ eE)[As0 _]] := projT2 (cid (@Urysohn' A B)).
rewrite eqEsubset; split => // ? ->; case: Aa => a ?; exists a => //.
by apply: As0; exists a.
Qed.

Lemma Urysohn_eq1 (A B : set T) :
  uniform_separator A B -> (B !=set0) -> (Urysohn A B) @` B = [set 1].
Proof.
move=> eE Bb; have [_ _ /(_ eE)[_ Bs0]] := projT2 (cid (@Urysohn' A B)).
rewrite eqEsubset; split => // ? ->; case: Bb => b ?; exists b => //.
by apply: Bs0; exists b.
Qed.

End urysohn_facts.
End topological_urysohn_separator.

Lemma uniform_separatorW {T : uniformType} (A B : set T) :
    (exists2 E, entourage E & A `*` B `&` E = set0) ->
  uniform_separator A B.
Proof. by case=> E entE AB0; exists (Uniform.class T), E; split => // ?. Qed.

Section Urysohn.
Local Open Scope relation_scope.
Context {T : topologicalType}.
Hypothesis normalT : normal_space T.
Section normal_uniform_separators.
Context (A : set T).

(* Urysohn's lemma guarantees a continuous function : T -> R
   where "f @` A = [set 0]" and "f @` B = [set 1]".
   The idea is to leverage countable_uniformity to build that function
   rather than construct it directly.

   The bulk of the work is building a uniformity to measure "distance from A".
   Each pair of "nested" U,V induces an approximation "apxU".
                 A-------)] U
                 A----------------) V (points near A)
                          (------------  ~`closure U (points far from A)
   These make the sub-basis for a filter. That filter is a uniformity
   because normality lets us split

                 A------)] U
                 A-----------)]  V'
                         (---------------  ~`closure U
                 A----------------) V
                              (---------  ~` closure V'
   and (U,V') + (V', V) splits the entourage of (U,V). This uniform space is not
   neccesarily a pseudometric. So we find an entourage which divides A and B,
   then the gauge pseudometric gives us what we want.
*)

Let apxU (UV : set T * set T) : set (T * T) :=
  (UV.2 `*` UV.2) `|` (~` closure UV.1 `*` ~` closure UV.1).

Let nested (UV : set T * set T) :=
  [/\ open UV.1, open UV.2, A `<=` UV.1 & closure UV.1 `<=`UV.2].

Let ury_base := [set apxU UV | UV in nested].

Local Lemma ury_base_refl E : ury_base E -> diagonal `<=` E.
Proof.
case; case=> L R [_ _ _ /= LR] <- [? x /= /diagonalP ->].
case: (pselect (R x)); first by left.
by move/subsetC: LR => /[apply] => ?; right.
Qed.

Local Lemma ury_base_inv E : ury_base E -> ury_base E^-1.
Proof.
case; case=> L R ? <-; exists (L, R) => //.
by rewrite eqEsubset; split => //; (case=> x y [] [? ?]; [left| right]).
Qed.

Local Lemma ury_base_split E : ury_base E ->
  exists E1 E2, [/\ ury_base E1, ury_base E2 &
                    (E1 `&` E2) \; (E1 `&` E2) `<=` E].
Proof.
case; case => L R [/= oL oR AL cLR <-].
have [R' []] : exists R', [/\ open R', closure L `<=` R' & closure R' `<=` R].
  have := @normalT (closure L) (@closed_closure T L).
  case/(_ R); first by move=> x /cLR ?; apply: open_nbhs_nbhs.
  move=> V /set_nbhsP [U] [? ? ? cVR]; exists U; split => //.
  by apply: (subset_trans _ cVR); exact: closure_subset.
move=> oR' cLR' cR'R; exists (apxU (L, R')), (apxU (R', R)).
split; first by exists (L, R').
  exists (R', R) => //; split => //; apply: (subset_trans AL).
  by apply: (subset_trans _ cLR'); exact: subset_closure.
case=> x z /= [y [+ +] []].
(do 4 (case; case=> /= ? ?)); try (by left); try (by right);
  match goal with nG : (~ closure ?S ?y), G : ?S ?y |- _ =>
    by move/subset_closure: G
  end.
Qed.

Let ury_unif := smallest Filter ury_base.

Instance ury_unif_filter : Filter ury_unif.
Proof. exact: smallest_filter_filter. Qed.

Local Lemma ury_unif_refl E : ury_unif E -> diagonal `<=` E.
Proof.
by move/(_ (globally diagonal)); apply; split;
  [exact: globally_filter|exact: ury_base_refl].
Qed.

Local Lemma ury_unif_inv E : ury_unif E -> ury_unif E^-1.
Proof.
move=> ufE F [/filter_inv FF urF]; have [] := ufE [set V^-1 | V in F].
  split => // K /ury_base_inv/urF /= ?; exists (K^-1)%classic => //.
  by rewrite set_prod_invK.
by move=> R FR <-; rewrite set_prod_invK.
Qed.

Local Lemma ury_unif_split_iter E n :
  filterI_iter ury_base n E -> exists2 K : set (T * T),
    filterI_iter ury_base n.+1 K & K \; K `<=` E.
Proof.
elim: n E; first move=> E [].
- move=> ->; exists setT => //; exists setT; first by left.
  by exists setT; rewrite ?setIT; first by left.
- move=> /[dup] /ury_base_split [E1 [E2] [? ? ? ?]]; exists (E1 `&` E2) => //.
  by (exists E1; first by right); exists E2; first by right.
move=> n IH E /= [E1 /IH [F1 F1n1 F1E1]] [E2 /IH [F2 F2n1 F2E2]] E12E.
exists (F1 `&` F2); first by exists F1 => //; exists F2.
move=> /= [x z ] [y /= [K1xy K2xy] [K1yz K2yz]]; rewrite -E12E; split.
  by apply: F1E1; exists y.
by apply: F2E2; exists y.
Qed.

Local Lemma ury_unif_split E : ury_unif E ->
  exists2 K, ury_unif K & K \; K `<=` E.
Proof.
rewrite /ury_unif filterI_iterE; case=> G [n _] /ury_unif_split_iter [].
move=> K SnK KG GE; exists K; first by exists K => //; exists n.+1.
exact: (subset_trans _ GE).
Qed.

Local Lemma ury_unif_covA E : ury_unif E -> A `*` A `<=` E.
Proof.
rewrite /ury_unif filterI_iterE; case=> G [n _] sG /(subset_trans _); apply.
elim: n G sG.
  move=> g [-> //| [[P Q]]] [/= _ _ AP cPQ <-] [x y] [/= /AP ? ?].
  by left; split => //=; apply/cPQ/subset_closure => //; exact: AP.
by move=> n IH G [R] /IH AAR [M] /IH AAM <- z; split; [exact: AAR | exact: AAM].
Qed.

Definition urysohnType : Type := T.

HB.instance Definition _ := Choice.on urysohnType.

HB.instance Definition _ :=
  isUniform.Build urysohnType ury_unif_filter ury_unif_refl ury_unif_inv
  ury_unif_split.
HB.instance Definition _ {p : Pointed T} := Pointed.copy urysohnType (Pointed.Pack p).

Lemma normal_uniform_separator (B : set T) :
  closed A -> closed B -> A `&` B = set0 -> uniform_separator A B.
Proof.
move=> clA clB AB0; have /(_ (~`B))[x Ax|] := normalT clA.
  apply: open_nbhs_nbhs; split => //.
  - exact/closed_openC.
  - by move: x Ax; apply/ disjoints_subset.
move=> V /set_nbhsP [U [oU AU UV]] cVcb.
exists (Uniform.class urysohnType), (apxU (U, ~` B)); split => //.
- move=> ?; apply:sub_gen_smallest; exists (U, ~`B) => //; split => //=.
    exact/closed_openC.
  by move: UV => /closure_subset/subset_trans; apply.
- rewrite eqEsubset; split; case=> // a b [/=[Aa Bb] [[//]|]].
  by have /subset_closure ? := AU _ Aa; case.
move=> x ? [E gE] /(@filterS T); apply; move: gE.
rewrite /= /ury_unif filterI_iterE; case => K /= [i _] /= uiK KE.
suff : @nbhs T T x [set y | K (x, y)] by apply: filterS => y /KE/xsectionP.
elim: i K uiK {E KE}; last by move=> ? H ? [N] /H ? [M] /H ? <-; apply: filterI.
move=> K [->|]; first exact: filterT.
move=> [[/= P Q] [/= oP oQ AP cPQ <-]]; rewrite /apxU /=.
set M := [set y | _ \/ _].
have [Qx|nQx] := pselect (Q x); first last.
  suff -> : M = ~` closure P.
    apply: open_nbhs_nbhs; split; first exact/closed_openC/closed_closure.
    by move/cPQ.
  rewrite eqEsubset /M; split => z; first by do 2!case.
  by move=> ?; right; split => // /cPQ.
have [nPx|cPx] := pselect (closure P x).
  suff -> : M = Q by apply: open_nbhs_nbhs; split.
  rewrite eqEsubset /M; split => z; first by do 2!case.
  by move=> ?; left; split.
suff -> : M = setT by exact: filterT.
rewrite eqEsubset; split => // z _.
by have [Qz|/(subsetC cPQ)] := pselect (Q z); constructor.
Qed.

End normal_uniform_separators.
End Urysohn.

Lemma uniform_separatorP {T : topologicalType} {R : realType} (A B : set T) :
  uniform_separator A B <->
  exists (f : T -> R), [/\ continuous f, range f `<=` `[0, 1],
                           f @` A `<=` [set 0] & f @` B `<=` [set 1]].
Proof.
split; first do [move=> ?; exists (Urysohn A B); split].
- exact: Urysohn_continuous.
- exact: Urysohn_range.
- exact: Urysohn_sub0.
- exact: Urysohn_sub1.
case=> f [ctsf f01 fA0 fB1].
pose T' : uniformType := weak_topology f.
exists (Uniform.class T'), ([set xy | ball (f xy.1) 1 (f xy.2)]); split.
- exists [set xy | ball xy.1 1 xy.2]; last by case.
  by rewrite -entourage_ballE; exists 1 => //=.
- rewrite -subset0 => -[a b [[/= Aa Bb]]].
  by rewrite (imsub1 fA0)// (imsub1 fB1)// /ball/= sub0r normrN normr1 ltxx.
- move=> x U [V [[W oW <- /=]]] ? /filterS; apply.
  by apply: ctsf; exact: open_nbhs_nbhs.
Qed.

Section normalP.
Context {R : realType} {T : topologicalType}.

(* Ideally, R should be an instance of realType here,
   rather than a section variable. *)
Let normal_spaceP : [<->
  (* 0 *) normal_space T;
  (* 1 *) forall (A B : set T), closed A -> closed B -> A `&` B = set0 ->
    uniform_separator A B;
  (* 2 *) forall (A B : set T), closed A -> closed B -> A `&` B = set0 ->
    exists U V, [/\ open U, open V, A `<=` U, B `<=` V & U `&` V = set0] ].
Proof.
tfae; first by move=> ?; exact: normal_uniform_separator.
- move=> + A B clA clB AB0 => /(_ _ _ clA clB AB0) /(@uniform_separatorP _ R).
  case=> f [cf f01 /imsub1P/subset_trans fa0 /imsub1P/subset_trans fb1].
  exists (f@^-1` `]-1, 1/2[), (f @^-1` `]1/2, 2[); split.
  + by apply: open_comp; [|exact: interval_open].
  + by apply: open_comp; [|exact: interval_open].
  + by apply: fa0 => x/= ->; rewrite (@in_itv _ R)/=; apply/andP; split.
  + apply: fb1 => x/= ->; rewrite (@in_itv _ R)/= ltr_pdivrMr// mul1r.
    by rewrite ltr1n.
  + rewrite -preimage_setI ?set_itvoo -subset0 => t [] /andP [_ +] /andP [+ _].
    by move=> /lt_trans /[apply]; rewrite ltxx.
move=> + A clA B /set_nbhsP [C [oC AC CB]].
have AC0 : A `&` ~` C = set0 by apply/disjoints_subset; rewrite setCK.
case/(_ _ _ clA (open_closedC oC) AC0) => U [V] [oU oV AU nCV UV0].
exists (~` closure V).
  apply/set_nbhsP; exists U; split => //.
  apply/subsetCr; have := open_closedC oU; rewrite closure_id => ->.
  by apply/closure_subset/disjoints_subset; rewrite setIC.
apply/(subset_trans _ CB)/subsetCP; apply: (subset_trans nCV).
apply/subsetCr; have := open_closedC oV; rewrite closure_id => ->.
exact/closure_subset/subsetC/subset_closure.
Qed.

Lemma normal_openP : normal_space T <->
  forall (A B : set T), closed A -> closed B -> A `&` B = set0 ->
  exists U V, [/\ open U, open V, A `<=` U, B `<=` V & U `&` V = set0].
Proof. exact: (normal_spaceP 0%N 2%N). Qed.

Lemma normal_separatorP : normal_space T <->
  forall (A B : set T), closed A -> closed B -> A `&` B = set0 ->
  uniform_separator A B.
Proof. exact: (normal_spaceP 0%N 1%N). Qed.

End normalP.

Section completely_regular.
Context {R : realType}.

(**md This is equivalent to uniformizable. Note there is a subtle
   distinction between being uniformizable and being uniformType.
   There is often more than one possible uniformity, and being a
   uniformType has a specific one.

   If you don't care, you can use the `completely_regular_uniformity.type`
   which builds the uniformity.
*)
Definition completely_regular_space (T : topologicalType) :=
  forall (a : T) (B : set T), closed B -> ~ B a -> uniform_separator [set a] B.

Lemma point_uniform_separator {T : uniformType} (x : T) (B : set T) :
  closed B -> ~ B x -> uniform_separator [set x] B.
Proof.
move=> clB nBx; have : open (~` B) by rewrite openC.
rewrite openE => /(_ _ nBx); rewrite /interior /= -nbhs_entourageE.
case=> E entE EnB.
pose T' : pseudoMetricType R := gauge.type entE.
exists (Uniform.class T); exists E; split => //; last by move => ?.
by rewrite -subset0 => -[? w [/= [-> ? /xsectionP ?]]]; exact: (EnB w).
Qed.

Lemma uniform_completely_regular {T : uniformType} :
  @completely_regular_space T.
Proof. by move=> x B clB Bx; exact: point_uniform_separator. Qed.

Lemma normal_completely_regular {T : topologicalType} :
  normal_space T -> accessible_space T -> completely_regular_space T.
Proof.
move/normal_separatorP => + /accessible_closed_set1 cl1 x A ? ?; apply => //.
by apply/disjoints_subset => ? ->.
Qed.

Lemma uniform_regular {X : uniformType} : @regular_space X.
Proof.
move=> x A; rewrite /= -nbhs_entourageE => -[E entE].
move/(subset_trans (ent_closure entE)) => ExA.
by exists (xsection (split_ent E) x) => //; exists (split_ent E).
Qed.

End completely_regular.

Module completely_regular_uniformity.
Section completely_regular_uniformity.
Context {R : realType} {X : topologicalType}.
Hypothesis crs : completely_regular_space X.

Let X' : uniformType := @sup_topology X {f : X -> R | continuous f}
  (fun f => Uniform.class (weak_topology (projT1 f))).

Let completely_regular_nbhsE : @nbhs X X = nbhs_ (@entourage X').
Proof.
rewrite nbhs_entourageE; apply/funext => x; apply/seteqP; split; first last.
  apply/cvg_sup => -[f ctsf] U [/= _ [[V /= oV <- /= Vfx]]] /filterS.
  by apply; exact/ctsf/open_nbhs_nbhs.
move=> U; wlog oU : U / @open X U.
  move=> WH; rewrite nbhsE => -[V [oV Vx /filterS]].
  apply; first exact: (@nbhs_filter X').
  by apply: WH => //; move: oV; rewrite openE; exact.
move=> /[dup] nUx /nbhs_singleton Ux.
have ufs : uniform_separator [set x] (~` U).
  by apply: crs; [exact: open_closedC | exact].
have /uniform_separatorP := ufs => /(_ R)[f [ctsf f01 fx0 fU1]].
rewrite -nbhs_entourageE /entourage /= /sup_ent /= smallest_filter_finI.
pose E := map_pair f @^-1` (fun pq => ball pq.1 1 pq.2).
exists E; first last.
  move=> z /= /set_mem; rewrite /E /=.
  have -> : f x = 0 by apply: fx0; exists x.
  rewrite /ball /= sub0r normrN; apply: contraPP => cUz.
  suff -> : f z = 1 by rewrite normr1 ltxx.
  by apply: fU1; exists z.
move=> r /= [_]; apply => /=.
pose f' : {classic {f : X -> R | continuous f}} := exist _ f ctsf.
suff /asboolP entE : @entourage (weak_topology f) (f', E).2.
  by exists (exist _ (f', E) entE).
exists (fun pq => ball pq.1 1 pq.2) => //=.
by rewrite /entourage /=; exists 1 => /=.
Qed.

Definition type : Type := let _ := completely_regular_nbhsE in X.

#[export] HB.instance Definition _ := Topological.copy type X.
#[export] HB.instance Definition _ := @Nbhs_isUniform.Build
  type
  (@entourage X')
  (@entourage_filter X')
  (@entourage_diagonal_subproof X')
  (@entourage_inv X')
  (@entourage_split_ex X')
  completely_regular_nbhsE.
#[export] HB.instance Definition _ := Uniform.on type.

End completely_regular_uniformity.
Module Exports. HB.reexport. End Exports.
End completely_regular_uniformity.
Export completely_regular_uniformity.Exports.

Section locally_compact_uniform.
Context {X : topologicalType} {R : realType}.
Hypothesis lcpt : locally_compact [set: X].
Hypothesis hsdf : hausdorff_space X.

Let opc := @one_point_compactification X.

Lemma one_point_compactification_completely_reg :
  completely_regular_space opc.
Proof.
apply: (@normal_completely_regular R).
  apply: compact_normal.
    exact: one_point_compactification_hausdorff.
  exact: one_point_compactification_compact.
by apply: hausdorff_accessible; exact: one_point_compactification_hausdorff.
Qed.

#[local]
HB.instance Definition _ := Uniform.copy opc
  (@completely_regular_uniformity.type R _
    one_point_compactification_completely_reg).

Let X' := @weak_topology X opc Some.
Lemma nbhs_one_point_compactification_weakE : @nbhs X X = nbhs_ (@entourage X').
Proof. by rewrite nbhs_entourageE one_point_compactification_weak_topology. Qed.

#[local, non_forgetful_inheritance]
HB.instance Definition _ := @Nbhs_isUniform.Build
  X
  (@entourage X')
  (@entourage_filter X')
  (@entourage_diagonal_subproof X')
  (@entourage_inv X')
  (@entourage_split_ex X')
  nbhs_one_point_compactification_weakE.

Lemma locally_compact_completely_regular : completely_regular_space X.
Proof. exact: uniform_completely_regular. Qed.

End locally_compact_uniform.

Lemma completely_regular_regular {R : realType} {X : topologicalType} :
  completely_regular_space X -> @regular_space X.
Proof.
move=> crsX; pose P' := @completely_regular_uniformity.type R _ crsX.
exact: (@uniform_regular P').
Qed.

Section pseudometric_normal.

Lemma regular_openP {T : topologicalType} (x : T) :
  {for x, @regular_space T} <-> forall A, closed A -> ~ A x ->
  exists U V : set T, [/\ open U, open V, U x, A `<=` V & U `&` V = set0].
Proof.
split.
  move=> + A clA nAx => /(_ (~` A)) [].
    by apply: open_nbhs_nbhs; split => //; exact: closed_openC.
  move=> U Ux /subsetC; rewrite setCK => AclU; exists U^°.
  exists (~` closure U) ; split => //; first exact: open_interior.
    exact/closed_openC/closed_closure.
  apply/disjoints_subset; rewrite setCK.
  exact: (subset_trans (@interior_subset _ _) (@subset_closure _ _)).
move=> + A Ax => /(_ (~` A^°)) []; [|exact|].
  exact/open_closedC/open_interior.
move=> U [V] [oU oV Ux /subsetC cAV /disjoints_subset UV]; exists U.
  exact/open_nbhs_nbhs.
apply: (subset_trans (closure_subset UV)).
move/open_closedC/closure_id : oV => <-.
by apply: (subset_trans cAV); rewrite setCK; exact: interior_subset.
Qed.

Lemma pseudometric_normal {R : realType} {X : pseudoMetricType R} :
  normal_space X.
Proof.
apply/(@normal_openP R) => A B clA clB AB0.
have eps' (D : set X) : closed D -> forall x, exists eps : {posnum R}, ~ D x ->
    ball x eps%:num `&` D = set0.
  move=> clD x; have [nDx|?] := pselect (~ D x); last by exists 1%:pos.
  have /regular_openP/(_ _ clD) [//|] := @uniform_regular X x.
  move=> U [V] [+ oV] Ux /subsetC BV /disjoints_subset UV0.
  rewrite openE /interior => /(_ _ Ux); rewrite -nbhs_ballE => -[].
  move => _/posnumP[eps] beU; exists eps => _; apply/disjoints_subset.
  exact: (subset_trans beU (subset_trans UV0 _)).
pose epsA x := projT1 (cid (eps' _ clB x)).
pose epsB x := projT1 (cid (eps' _ clA x)).
exists (\bigcup_(x in A) interior (ball x ((epsA x)%:num / 2)%:pos%:num)).
exists (\bigcup_(x in B) interior (ball x ((epsB x)%:num / 2)%:pos%:num)).
split.
- by apply: bigcup_open => ? ?; exact: open_interior.
- by apply: bigcup_open => ? ?; exact: open_interior.
- by move=> x ?; exists x => //; exact: nbhsx_ballx.
- by move=> y ?; exists y => //; exact: nbhsx_ballx.
- apply/eqP/negPn/negP/set0P => -[z [[x Ax /interior_subset Axe]]].
  case=> y By /interior_subset Bye; have nAy : ~ A y.
    by move: AB0; rewrite setIC => /disjoints_subset; exact.
  have nBx : ~ B x by move/disjoints_subset: AB0; exact.
  have [|/ltW] := leP ((epsA x)%:num / 2) ((epsB y)%:num / 2).
    move/ball_sym: Axe => /[swap] /le_ball /[apply] /(ball_triangle Bye).
    rewrite -splitr => byx; have := projT2 (cid (eps' _ clA y)) nAy.
    by rewrite -subset0; apply; split; [exact: byx|].
  move/ball_sym: Bye =>/[swap] /le_ball /[apply] /(ball_triangle Axe).
  rewrite -splitr => byx; have := projT2 (cid (eps' _ clB x)) nBx.
  by rewrite -subset0; apply; split; [exact: byx|].
Qed.

End pseudometric_normal.

Section open_closed_sets_ereal.
Variable R : realFieldType (* TODO: generalize to numFieldType? *).
Local Open Scope ereal_scope.
Implicit Types x y : \bar R.
Implicit Types r : R.

Lemma open_ereal_lt y : open [set r : R | r%:E < y].
Proof.
case: y => [y||] /=; first exact: open_lt.
- rewrite (_ : [set _ | _] = setT); first exact: openT.
  by rewrite funeqE => ? /=; rewrite ltry trueE.
- rewrite (_ : [set _ | _] = set0); first exact: open0.
  by rewrite funeqE => ? /=; rewrite falseE.
Qed.

Lemma open_ereal_gt y : open [set r : R | y < r%:E].
Proof.
case: y => [y||] /=; first exact: open_gt.
- rewrite (_ : [set _ | _] = set0); first exact: open0.
  by rewrite funeqE => ? /=; rewrite falseE.
- rewrite (_ : [set _ | _] = setT); first exact: openT.
  by rewrite funeqE => ? /=; rewrite ltNyr trueE.
Qed.

Lemma open_ereal_lt' x y : x < y -> ereal_nbhs x (fun u => u < y).
Proof.
case: x => [x|//|] xy; first exact: open_ereal_lt.
- case: y => [y||//] /= in xy *; last by exists 0%R.
  by exists y; rewrite num_real; split => //= x ?.
- case: y => [y||//] /= in xy *.
  + by exists y; rewrite num_real; split => //= x ?.
  + by exists 0%R; split => // x /lt_le_trans; apply; rewrite leey.
Qed.

Lemma open_ereal_gt' x y : y < x -> ereal_nbhs x (fun u => y < u).
Proof.
case: x => [x||] //=; do ?[exact: open_ereal_gt];
  case: y => [y||] //=; do ?by exists 0.
- by exists y; rewrite num_real.
- by move=> _; exists 0%R; split => // x; apply/le_lt_trans; rewrite leNye.
Qed.

Lemma open_ereal_lt_ereal x : open [set y | y < x].
Proof.
have openr r : open [set x : \bar R | x < r%:E].
  (* BUG: why doesn't case work? *)
  move=> [? | // | ?]; [rewrite /= lte_fin => xy | by exists r].
  by move: (@open_ereal_lt r%:E); rewrite openE; apply; rewrite /= lte_fin.
move: x => [ // | | ]; last by move=> []. (* same BUG *)
suff -> : [set y | y < +oo] = \bigcup_r [set y : \bar R | y < r%:E].
  exact: bigcup_open.
rewrite predeqE => -[r | | ]/=.
- rewrite ltry; split => // _.
  by exists (r + 1)%R => //=; rewrite lte_fin ltrDl.
- by rewrite ltxx; split => // -[] x /=; rewrite ltNge leey.
- by split => // _; exists 0%R => //=; rewrite ltNye.
Qed.

Lemma open_ereal_gt_ereal x : open [set y | x < y].
Proof.
have openr r : open [set x | r%:E < x].
  move=> [? | ? | //]; [rewrite /= lte_fin => xy | by exists r].
  by move: (@open_ereal_gt r%:E); rewrite openE; apply; rewrite /= lte_fin.
case: x => [ // | | ]; first by move=> [].
suff -> : [set y | -oo < y] = \bigcup_r [set y : \bar R | r%:E < y].
  exact: bigcup_open.
rewrite predeqE => -[r | | ]/=.
- rewrite ltNyr; split => // _.
  by exists (r - 1)%R => //=; rewrite lte_fin ltrBlDr ltrDl.
- by split => // _; exists 0%R => //=; rewrite ltey.
- by rewrite ltxx; split => // -[] x _ /=; rewrite ltNge leNye.
Qed.

Lemma closed_ereal_le_ereal y : closed [set x | y <= x].
Proof.
rewrite (_ : [set x | y <= x] = ~` [set x | y > x]); last first.
  by rewrite predeqE=> x; split=> [rx|/negP]; [apply/negP|]; rewrite -leNgt.
exact/open_closedC/open_ereal_lt_ereal.
Qed.

Lemma closed_ereal_ge_ereal y : closed [set x | y >= x].
Proof.
rewrite (_ : [set x | y >= x] = ~` [set x | y < x]); last first.
  by rewrite predeqE=> x; split=> [rx|/negP]; [apply/negP|]; rewrite -leNgt.
exact/open_closedC/open_ereal_gt_ereal.
Qed.

End open_closed_sets_ereal.

Section closure_left_right_open.
Variable R : realFieldType.
Implicit Types z : R.

Lemma closure_gt z : closure ([set x | z < x] : set R) = [set x | z <= x].
Proof.
rewrite eqEsubset; split.
  by rewrite closureE; apply: smallest_sub => // ? /ltW.
move=> v; rewrite /mkset le_eqVlt => /predU1P[<-{v}|]; last first.
  by move=> ?; exact: subset_closure.
move=> B [e /= e0 zB]; near (0 : R)^'+ => d.
exists (z + d); split; rewrite /= ?ltrDl//; apply: zB => /=.
by rewrite opprD addNKr normrN gtr0_norm//.
Unshelve. all: by end_near. Qed.

Lemma closure_lt z : closure ([set x : R | x < z]) = [set x | x <= z].
Proof.
rewrite eqEsubset; split.
  by rewrite closureE; apply: smallest_sub => // ? /ltW.
move=> v; rewrite /mkset le_eqVlt => /predU1P[<-{z}|]; last first.
  by move=> ?; exact: subset_closure.
move=> B [e /= e0 vB]; near (0 : R)^'+ => d.
exists (v - d); split; rewrite /= ?gtrDl ?oppr_lt0//; apply: vB => /=.
by rewrite opprB addrC addrNK gtr0_norm//; near: d.
Unshelve. all: by end_near. Qed.

End closure_left_right_open.

(** Complete Normed Modules *)

#[short(type="completeNormedModType")]
HB.structure Definition CompleteNormedModule (K : numFieldType) :=
  {T of NormedModule K T & Complete T}.

(** The topology on real numbers *)

Lemma R_complete (R : realType) (F : set_system R) :
  ProperFilter F -> cauchy F -> cvg F.
Proof.
move=> FF /cauchy_ballP F_cauchy; apply/cvg_ex.
pose D := \bigcap_(A in F) (down A).
have /cauchy_ballP /cauchyP /(_ 1) [//|x0 x01] := F_cauchy.
have D_has_sup : has_sup D; first split.
- exists (x0 - 1) => A FA.
  near F => x.
  apply/downP; exists x; first by near: x.
  by rewrite ler_distlBl // ltW //; near: x.
- exists (x0 + 1); apply/ubP => x /(_ _ x01) /downP [y].
  rewrite -[ball _ _ _]/(_ (_ < _)) ltr_distl ltrBlDr => /andP[/ltW].
  by move=> /(le_trans _) yx01 _ /yx01.
exists (sup D).
apply/cvgrPdist_le => /= _ /posnumP[eps]; near=> x.
rewrite ler_distl; move/ubP: (sup_upper_bound D_has_sup) => -> //=.
  apply: sup_le_ub => //; first by case: D_has_sup.
  have Fxeps : F (ball_ [eta normr] x eps%:num).
    by near: x; apply: nearP_dep; apply: F_cauchy.
  apply/ubP => y /(_ _ Fxeps) /downP[z].
  rewrite /ball_/= ltr_distl ltrBlDr.
  by move=> /andP [/ltW /(le_trans _) le_xeps _ /le_xeps].
rewrite /D /= => A FA; near F => y.
apply/downP; exists y.
by near: y.
rewrite lerBlDl -lerBlDr ltW //.
suff: `|x - y| < eps%:num by rewrite ltr_norml => /andP[_].
by near: y; near: x; apply: nearP_dep; apply: F_cauchy.
Unshelve. all: by end_near. Qed.

HB.instance Definition _ (R : realType) := Uniform_isComplete.Build R^o
  (@R_complete R). (* todo : delete *)

HB.instance Definition _ (R : realType) := Complete.copy R R^o.
(* new *)

Section cvg_seq_bounded.
Context {K : numFieldType}.
Local Notation "'+oo'" := (@pinfty_nbhs K).

Lemma cvg_seq_bounded {V : normedModType K} (a : nat -> V) :
  cvgn a -> bounded_fun a.
Proof.
move=> /cvg_bounded/ex_bound => -[/= Moo] => -[N _ /(_ _) aM].
have Moo_real : Moo \is Num.real by rewrite ger0_real ?(le_trans _ (aM N _))/=.
rewrite /bounded_near /=; near=> M => n _.
have [nN|nN]/= := leqP N n; first by apply: (le_trans (aM _ _)).
move: n nN; suff /(_ (Ordinal _)) : forall n : 'I_N, `|a n| <= M by [].
by near: M; apply: filter_forall => i; apply: nbhs_pinfty_ge.
Unshelve. all: by end_near. Qed.

End cvg_seq_bounded.

Lemma closure_sup (R : realType) (A : set R) :
  A !=set0 -> has_ubound A -> closure A (sup A).
Proof.
move=> A0 ?; have [|AsupA] := pselect (A (sup A)); first exact: subset_closure.
rewrite closure_limit_point; right => U /nbhs_ballP[_ /posnumP[e]] supAeU.
suff [x [Ax /andP[sAex xsA]]] : exists x, A x /\ sup A - e%:num < x < sup A.
  exists x; split => //; first by rewrite lt_eqF.
  apply supAeU; rewrite /ball /= ltr_distl (addrC x e%:num) -ltrBlDl sAex.
  by rewrite andbT (le_lt_trans _ xsA) // lerBlDl lerDr.
apply: contrapT => /forallNP Ax.
suff /(sup_le_ub A0) : ubound A (sup A - e%:num).
  by rewrite leNgt => /negP; apply; rewrite ltrBlDl ltrDr.
move=> y Ay; have /not_andP[//|/negP] := Ax y.
rewrite negb_and leNgt => /orP[//|]; apply: contra => sAey.
rewrite lt_neqAle sup_upper_bound // andbT.
by apply: contra_not_neq AsupA => <-.
Qed.

Lemma near_infty_natSinv_lt (R : archiFieldType) (e : {posnum R}) :
  \forall n \near \oo, n.+1%:R^-1 < e%:num.
Proof.
near=> n; rewrite -(@ltr_pM2r _ n.+1%:R) // mulVr ?unitfE //.
rewrite -(@ltr_pM2l _ e%:num^-1) // mulr1 mulrA mulVr ?unitfE // mul1r.
rewrite (lt_trans (archi_boundP _)) // ltr_nat.
by near: n; exists (Num.bound e%:num^-1).
Unshelve. all: by end_near. Qed.

Lemma near_infty_natSinv_expn_lt (R : archiFieldType) (e : {posnum R}) :
  \forall n \near \oo, 1 / 2 ^+ n < e%:num.
Proof.
near=> n.
rewrite -(@ltr_pM2r _ (2 ^+ n)) // -?natrX ?ltr0n ?expn_gt0//.
rewrite mul1r mulVr ?unitfE ?gt_eqF// ?ltr0n ?expn_gt0//.
rewrite -(@ltr_pM2l _ e%:num^-1) // mulr1 mulrA mulVr ?unitfE // mul1r.
rewrite (lt_trans (archi_boundP _)) // natrX upper_nthrootP //.
near: n; eexists; last by move=> m; exact.
by [].
Unshelve. all: by end_near. Qed.

Lemma limit_pointP (T : archiFieldType) (A : set T) (x : T) :
  limit_point A x <-> exists a_ : nat -> T,
    [/\ a_ @` setT `<=` A, forall n, a_ n != x & a_ @ \oo --> x].
Proof.
split=> [Ax|[a_ [aTA a_x] ax]]; last first.
  move=> U /ax[m _ a_U]; near \oo => n; exists (a_ n); split => //.
  by apply aTA; exists n.
  by apply a_U; near: n; exists m.
pose U := fun n : nat => [set z : T | `|x - z| < n.+1%:R^-1].
suff /(_ _)/cid-/all_sig[a_ anx] : forall n, exists a, a != x /\ (U n `&` A) a.
  exists a_; split.
  - by move=> a [n _ <-]; have [? []] := anx n.
  - by move=> n; have [] := anx n.
  - apply/cvgrPdist_lt => _/posnumP[e]; near=> n;  have [? [] Uan Aan] := anx n.
    by rewrite (lt_le_trans Uan)// ltW//; near: n; exact: near_infty_natSinv_lt.
move=> n; have : nbhs (x : T) (U n).
  by apply/(nbhs_ballP (x:T) (U n)); rewrite nbhs_ballE; exists n.+1%:R^-1 => //=.
by move/Ax/cid => [/= an [anx Aan Uan]]; exists an.
Unshelve. all: by end_near. Qed.

Section interval.
Variable R : numDomainType.

Definition is_interval (E : set R) :=
  forall x y, E x -> E y -> forall z, x <= z <= y -> E z.

Lemma is_intervalPlt (E : set R) :
  is_interval E <-> forall x y, E x -> E y -> forall z, x < z < y -> E z.
Proof.
split=> iE x y Ex Ey z /andP[].
  by move=> xz zy; apply: (iE x y); rewrite ?ltW.
rewrite !le_eqVlt => /predU1P[<-//|xz] /predU1P[->//|zy].
by apply: (iE x y); rewrite ?xz.
Qed.

Lemma interval_is_interval (i : interval R) : is_interval [set` i].
Proof.
by case: i => -[[]a|[]] [[]b|[]] // x y /=; do ?[by rewrite ?itv_ge//];
  move=> xi yi z; rewrite -[x <= z <= y]/(z \in `[x, y]); apply/subitvP;
  rewrite subitvE /Order.le/= ?(itvP xi, itvP yi).
Qed.

End interval.

Section ereal_is_hausdorff.
Variable R : realFieldType.
Implicit Types r : R.

Lemma nbhs_image_EFin (x : R) (X : set R) :
  nbhs x X -> nbhs x%:E ((fun r => r%:E) @` X).
Proof.
case => _/posnumP[e] xeX; exists e%:num => //= r xer.
by exists r => //; apply xeX.
Qed.

Lemma nbhs_open_ereal_lt r (f : R -> R) : r < f r ->
  nbhs r%:E [set y | y < (f r)%:E]%E.
Proof.
move=> xfx; rewrite nbhsE /=; eexists; last by move=> y; exact.
by split; [apply open_ereal_lt_ereal | rewrite /= lte_fin].
Qed.

Lemma nbhs_open_ereal_gt r (f : R -> R) : f r < r ->
  nbhs r%:E [set y | (f r)%:E < y]%E.
Proof.
move=> xfx; rewrite nbhsE /=; eexists; last by move=> y; exact.
by split; [apply open_ereal_gt_ereal | rewrite /= lte_fin].
Qed.

Lemma nbhs_open_ereal_pinfty r : (nbhs +oo [set y | r%:E < y])%E.
Proof.
rewrite nbhsE /=; eexists; last by move=> y; exact.
by split; [apply open_ereal_gt_ereal | rewrite /= ltry].
Qed.

Lemma nbhs_open_ereal_ninfty r : (nbhs -oo [set y | y < r%:E])%E.
Proof.
rewrite nbhsE /=; eexists; last by move=> y; exact.
by split; [apply open_ereal_lt_ereal | rewrite /= ltNyr].
Qed.

Lemma ereal_hausdorff : hausdorff_space (\bar R).
Proof.
move=> -[r| |] // [r' | |] //=.
- move=> rr'; congr (_%:E); apply Rhausdorff => /= A B rA r'B.
  have [/= z [[r0 ? r0z] [r1 ?]]] :=
    rr' _ _ (nbhs_image_EFin rA) (nbhs_image_EFin r'B).
  by rewrite -r0z => -[r1r0]; exists r0; split => //; rewrite -r1r0.
- have /(@nbhs_open_ereal_lt _ (fun x => x + 1)) loc_r : r < r + 1.
    by rewrite ltrDl.
  move/(_ _ _ loc_r (nbhs_open_ereal_pinfty (r + 1))) => -[z [zr rz]].
  by move: (lt_trans rz zr); rewrite lte_fin ltxx.
- have /(@nbhs_open_ereal_gt _ (fun x => x - 1)) loc_r : r - 1 < r.
    by rewrite ltrBlDr ltrDl.
  move/(_ _ _ loc_r (nbhs_open_ereal_ninfty (r - 1))) => -[z [rz zr]].
  by move: (lt_trans zr rz); rewrite ltxx.
- have /(@nbhs_open_ereal_lt _ (fun x => x + 1)) loc_r' : r' < r' + 1.
    by rewrite ltrDl.
  move/(_ _ _ (nbhs_open_ereal_pinfty (r' + 1)) loc_r') => -[z [r'z zr']].
  by move: (lt_trans zr' r'z); rewrite ltxx.
- move/(_ _ _ (nbhs_open_ereal_pinfty 0) (nbhs_open_ereal_ninfty 0)).
  by move=> -[z [zx xz]]; move: (lt_trans xz zx); rewrite ltxx.
- have /(@nbhs_open_ereal_gt _ (fun x => x - 1)) yB : r' - 1 < r'.
    by rewrite ltrBlDr ltrDl.
  move/(_ _ _ (nbhs_open_ereal_ninfty (r' - 1)) yB) => -[z [zr' r'z]].
  by move: (lt_trans r'z zr'); rewrite ltxx.
- move/(_ _ _ (nbhs_open_ereal_ninfty 0) (nbhs_open_ereal_pinfty 0)).
  by move=> -[z [zO Oz]]; move: (lt_trans Oz zO); rewrite ltxx.
Qed.

End ereal_is_hausdorff.

#[global]
Hint Extern 0 (hausdorff_space _) => solve[apply: ereal_hausdorff] : core.

Lemma EFin_lim (R : realFieldType) (f : nat -> R) : cvgn f ->
  limn (EFin \o f) = (limn f)%:E.
Proof.
move=> cf; apply: cvg_lim => //; move/cvg_ex : cf => [l fl].
by apply: (cvg_comp fl); rewrite (cvg_lim _ fl).
Qed.

Section ProperFilterERealType.
Context {T : Type} {a : set_system T} {Fa : ProperFilter a} {R : realFieldType}.
Local Open Scope ereal_scope.
Implicit Types f g h : T -> \bar R.

Lemma cvge_to_ge f b c : f @ a --> c -> (\near a, b <= f a) -> b <= c.
Proof.
by move=> /[swap]/(closed_cvg _ (@closed_ereal_le_ereal _ b)) /[apply].
Qed.

Lemma cvge_to_le f b c : f @ a --> c -> (\near a, f a <= b) -> c <= b.
Proof.
by move=> /[swap]/(closed_cvg _ (@closed_ereal_ge_ereal _ b))/[apply].
Qed.

Lemma lime_ge x f : cvg (f @ a) -> (\near a, x <= f a) -> x <= lim (f @ a).
Proof. exact: cvge_to_ge. Qed.

Lemma lime_le x f : cvg (f @ a) -> (\near a, x >= f a) -> x >= lim (f @ a).
Proof. exact: cvge_to_le. Qed.

End ProperFilterERealType.

Section ecvg_realFieldType_proper.
Context {I} {F : set_system I} {FF : ProperFilter F} {R : realFieldType}.
Implicit Types (f g : I -> \bar R) (u v : I -> R) (x : \bar R) (r : R).
Local Open Scope ereal_scope.

Lemma is_cvgeD f g :
  lim (f @ F) +? lim (g @ F) -> cvg (f @ F) -> cvg (g @ F) -> cvg (f \+ g @ F).
Proof. by move=> fg fc gc; have /(_ _)/cvgP := cvgeD fg fc gc. Qed.

Lemma limeD f g :
  cvg (f @ F) -> cvg (g @ F) -> lim (f @ F) +? lim (g @ F) ->
  lim (f \+ g @ F) = lim (f @ F) + lim (g @ F).
Proof. by move=> cf cg fg; apply/cvg_lim => //; exact: cvgeD. Qed.

Lemma limeMl f y : y \is a fin_num -> cvg (f @ F) ->
  lim ((fun n => y * f n) @ F) = y * lim (f @ F).
Proof. by move=> yfn cf; apply/cvg_lim => //; exact: cvgeMl. Qed.

Lemma limeMr f y : y \is a fin_num -> cvg (f @ F) ->
  lim ((fun n => f n * y) @ F) = lim (f @ F) * y.
Proof. by move=> yfn cf; apply/cvg_lim => //; apply: cvgeMr. Qed.

Lemma is_cvgeM f g :
  lim (f @ F) *? lim (g @ F) -> cvg (f @ F) -> cvg (g @ F) -> cvg (f \* g @ F).
Proof. by move=> fg fc gc; have /(_ _)/cvgP := cvgeM fg fc gc. Qed.

Lemma limeM f g :
  cvg (f @ F) -> cvg (g @ F) -> lim (f @ F) *? lim (g @ F) ->
  lim (f \* g @ F) = lim (f @ F) * lim (g @ F).
Proof. by move=> cf cg fg; apply/cvg_lim => //; exact: cvgeM. Qed.

Lemma limeN f : cvg (f @ F) -> lim (\- f @ F) = - lim (f @ F).
Proof. by move=> cf; apply/cvg_lim => //; apply: cvgeN. Qed.

Lemma cvge_ge f a b : (\forall x \near F, b <= f x) -> f @ F --> a -> b <= a.
Proof. by move=> ? fa; rewrite -(cvg_lim _ fa) ?lime_ge//=; apply: cvgP fa. Qed.

Lemma cvge_le f a b : (\forall x \near F, b >= f x) -> f @ F --> a -> b >= a.
Proof. by move=> ? fa; rewrite -(cvg_lim _ fa) ?lime_le//=; apply: cvgP fa. Qed.

Lemma cvg_nnesum (J : Type) (r : seq J) (f : J -> I -> \bar R)
   (l : J -> \bar R) (P : pred J) :
  (forall j, P j -> \near F, 0 <= f j F) ->
  (forall j, P j -> f j @ F --> l j) ->
  \sum_(j <- r | P j) f j i @[i --> F] --> \sum_(j <- r | P j) l j.
Proof.
pose bigsimp := (big_nil, big_cons);
elim: r => [|x r IHr]/= f0 fl; rewrite bigsimp; under eq_fun do rewrite bigsimp.
  exact: cvg_cst.
case: ifPn => [Px|Pnx]; last exact: IHr.
apply: cvgeD; [|exact: fl|exact: IHr].
by rewrite ge0_adde_def ?inE// ?sume_ge0// => [|j Pj];
   rewrite (cvge_ge _ (fl _ _))//; apply: f0.
Qed.

Lemma lim_nnesum (J : Type) (r : seq J) (f : J -> I -> \bar R)
   (l : J -> \bar R) (P : pred J) :
  (forall j, P j -> \near F, 0 <= f j F) ->
  (forall j, P j -> cvg (f j @ F)) ->
  lim (\sum_(j <- r | P j) f j i @[i --> F]) = \sum_(j <- r | P j) (lim (f j @ F)).
Proof. by move=> ? ?; apply/cvg_lim => //; apply: cvg_nnesum. Qed.

End ecvg_realFieldType_proper.

Section cvg_0_pinfty.
Context {R : realFieldType} {I : Type} {a : set_system I} {FF : Filter a}.
Implicit Types f : I -> R.

Lemma gtr0_cvgV0 f : (\near a, 0 < f a) -> f\^-1 @ a --> 0 <-> f @ a --> +oo.
Proof.
move=> f_gt0; split; last first.
  move=> /cvgryPgt cvg_f_oo; apply/cvgr0Pnorm_lt => _/posnumP[e].
  near=> i; rewrite gtr0_norm ?invr_gt0//=; last by near: i.
  by rewrite -ltf_pV2 ?qualifE/= ?invr_gt0 ?invrK//=; near: i.
move=> /cvgr0Pnorm_lt uB; apply/cvgryPgty.
near=> M; near=> i; suff: `|(f i)^-1| < M^-1.
  by rewrite gtr0_norm ?ltf_pV2 ?qualifE ?invr_gt0//=; near: i.
by near: i; apply: uB; rewrite ?invr_gt0.
Unshelve. all: by end_near. Qed.

Lemma cvgrVy f : (\near a, 0 < f a) -> f\^-1 @ a --> +oo <-> f @ a --> 0.
Proof.
by move=> f_gt0; rewrite -gtr0_cvgV0 ?inv_funK//; near do rewrite invr_gt0.
Unshelve. all: by end_near. Qed.

Lemma ltr0_cvgV0 f : (\near a, 0 > f a) -> f\^-1 @ a --> 0 <-> f @ a --> -oo.
Proof.
move=> fL0; rewrite -cvgNP oppr0 (_ : - f\^-1 =  (- f)\^-1); last first.
   by apply/funeqP => i; rewrite opprfctE/= invrN.
by rewrite gtr0_cvgV0 ?cvgNry//; near do rewrite oppr_gt0.
Unshelve. all: by end_near. Qed.

Lemma cvgrVNy f : (\near a, 0 > f a) -> f\^-1 @ a --> -oo <-> f @ a --> 0.
Proof.
by move=> f_lt0; rewrite -ltr0_cvgV0 ?inv_funK//; near do rewrite invr_lt0.
Unshelve. all: by end_near. Qed.

End cvg_0_pinfty.

Section FilterRealType.
Context {T : Type} {a : set_system T} {Fa : Filter a} {R : realFieldType}.
Implicit Types f g h : T -> R.

Lemma squeeze_cvgr f h g : (\near a, f a <= g a <= h a) ->
  forall (l : R), f @ a --> l -> h @ a --> l -> g @ a --> l.
Proof.
move=> fgh l lfa lga; apply/cvgrPdist_lt => e e_gt0.
near=> x; have /(_ _)/andP[//|fg gh] := near fgh x.
rewrite distrC ltr_distl (lt_le_trans _ fg) ?(le_lt_trans gh)//=.
  by near: x; apply: (cvgr_lt l); rewrite // ltrDl.
by near: x; apply: (cvgr_gt l); rewrite // gtrDl oppr_lt0.
Unshelve. all: end_near. Qed.

Lemma ger_cvgy f g : (\near a, f a <= g a) ->
  f @ a --> +oo -> g @ a --> +oo.
Proof.
move=> uv /cvgryPge ucvg; apply/cvgryPge => A.
by near=> x do rewrite (le_trans _ (near uv x _))//.
Unshelve. all: end_near. Qed.

Lemma ler_cvgNy f g : (\near a, f a >= g a) ->
  f @ a --> -oo -> g @ a --> -oo.
Proof.
move=> uv /cvgrNyPle ucvg; apply/cvgrNyPle => A.
by near=> x do rewrite (le_trans (near uv x _))//.
Unshelve. all: end_near. Qed.

End FilterRealType.

Section TopoProperFilterRealType.
Context {T : topologicalType} {a : set_system T} {Fa : ProperFilter a}.
Context {R : realFieldType}.
Implicit Types f g h : T -> R.

Lemma ler_cvg_to f g (l l' : R) : f @ a --> l -> g @ a --> l' ->
  (\near a, f a <= g a) -> l <= l'.
Proof.
move=> fl gl; under eq_near do rewrite -subr_ge0; rewrite -subr_ge0.
by apply: cvgr_to_ge; apply: cvgB.
Qed.

Lemma ler_lim f g : cvg (f @ a) -> cvg (g @ a) ->
  (\near a, f a <= g a) -> lim (f @ a) <= lim (g @ a).
Proof. exact: ler_cvg_to. Qed.

End TopoProperFilterRealType.

Section FilterERealType.
Context {T : Type} {a : set_system T} {Fa : Filter a} {R : realFieldType}.
Local Open Scope ereal_scope.
Implicit Types f g h : T -> \bar R.

Lemma gee_cvgy f g : (\near a, f a <= g a) ->
  f @ a --> +oo -> g @ a --> +oo.
Proof.
move=> uv /cvgeyPge uecvg; apply/cvgeyPge => A.
by near=> x do rewrite (le_trans _ (near uv x _))//.
Unshelve. all: end_near. Qed.

Lemma lee_cvgNy f g : (\near a, f a >= g a) ->
  f @ a --> -oo -> g @ a --> -oo.
Proof.
move=> uv /cvgeNyPle uecvg; apply/cvgeNyPle => A.
by near=> x do rewrite (le_trans (near uv x _))//.
Unshelve. all: end_near. Qed.

Lemma squeeze_fin f g h : (\near a, f a <= g a <= h a) ->
    (\near a, f a \is a fin_num) -> (\near a, h a \is a fin_num) ->
  (\near a, g a \is a fin_num).
Proof.
apply: filterS3 => x /andP[fg gh].
rewrite !fin_numElt => /andP[oof _] /andP[_ hoo].
by rewrite (lt_le_trans oof) ?(le_lt_trans gh).
Qed.

Lemma squeeze_cvge f g h : (\near a, f a <= g a <= h a) ->
  forall (l : \bar R), f @ a --> l -> h @ a --> l -> g @ a --> l.
Proof.
move=> fgh [l||]; last 2 first.
- by move=> + _; apply: gee_cvgy; apply: filterS fgh => ? /andP[].
- by move=> _; apply: lee_cvgNy; apply: filterS fgh => ? /andP[].
move=> /fine_cvgP[Ff fl] /fine_cvgP[Fh hl]; apply/fine_cvgP.
have Fg := squeeze_fin fgh Ff Fh; split=> //.
apply: squeeze_cvgr fl hl; near=> x => /=.
by have /(_ _)/andP[//|fg gh] := near fgh x; rewrite !fine_le//=; near: x.
Unshelve. all: end_near. Qed.

End FilterERealType.

Section TopoProperFilterERealType.
Context {T : topologicalType} {a : set_system T} {Fa : ProperFilter a}.
Context {R : realFieldType}.
Local Open Scope ereal_scope.
Implicit Types f g h : T -> \bar R.

Lemma lee_cvg_to f g l l' : f @ a --> l -> g @ a --> l' ->
  (\near a, f a <= g a) -> l <= l'.
Proof.
move=> + + fg; move: l' l.
move=> /= [l'||] [l||]//=; rewrite ?leNye ?leey//=; first 1 last.
- by move=> /(gee_cvgy fg) /cvg_lim<-// /cvg_lim<-.
- by move=> /cvg_lim <-// /(lee_cvgNy fg) /cvg_lim<-.
- by move=> /(gee_cvgy fg) /cvg_lim<-// /cvg_lim<-.
move=> /fine_cvgP[Ff fl] /fine_cvgP[Fg gl].
rewrite lee_fin -(cvg_lim _ fl)// -(cvg_lim _ gl)//.
by apply: ler_lim; [apply: cvgP fl|apply: cvgP gl|near do apply: fine_le].
Unshelve. all: end_near. Qed.

Lemma lee_lim f g : cvg (f @ a) -> cvg (g @ a) ->
  (\near a, f a <= g a) -> lim (f @ a) <= lim (g @ a).
Proof. exact: lee_cvg_to. Qed.

End TopoProperFilterERealType.

Section open_union_rat.
Variable R : realType.
Implicit Types A U : set R.

Let ointsub A U := [/\ open A, is_interval A & A `<=` U].

Let ointsub_rat U q := [set A | ointsub A U /\ A (ratr q)].

Let ointsub_rat0 q : ointsub_rat set0 q = set0.
Proof. by apply/seteqP; split => // A [[_ _]]; rewrite subset0 => ->. Qed.

Definition bigcup_ointsub U q := \bigcup_(A in ointsub_rat U q) A.

Lemma bigcup_ointsub0 q : bigcup_ointsub set0 q = set0.
Proof. by rewrite /bigcup_ointsub ointsub_rat0 bigcup_set0. Qed.

Lemma open_bigcup_ointsub U q : open (bigcup_ointsub U q).
Proof. by apply: bigcup_open => i [[]]. Qed.

Lemma is_interval_bigcup_ointsub U q : is_interval (bigcup_ointsub U q).
Proof.
move=> /= a b [A [[oA iA AU] Aq] Aa] [B [[oB iB BU] Bq] Bb] c /andP[ac cb].
have [cq|cq|->] := ltgtP c (ratr q); last by exists A.
- by exists A => //; apply: (iA a (ratr q)) => //; rewrite ac (ltW cq).
- by exists B => //; apply: (iB (ratr q) b) => //; rewrite cb (ltW cq).
Qed.

Lemma bigcup_ointsub_sub U q : bigcup_ointsub U q `<=` U.
Proof. by move=> y [A [[oA _ +] _ Ay]]; exact. Qed.

Lemma open_bigcup_rat U : open U ->
  U = \bigcup_(q in [set q | ratr q \in U]) bigcup_ointsub U q.
Proof.
move=> oU; have [->|U0] := eqVneq U set0.
  by rewrite bigcup0// => q _; rewrite bigcup_ointsub0.
apply/seteqP; split=> [x Ux|x [p _ Ipx]]; last exact: bigcup_ointsub_sub Ipx.
suff [q Iqx] : exists q, bigcup_ointsub U q x.
  by exists q => //=; rewrite in_setE; case: Iqx => A [[_ _ +] ? _]; exact.
have : nbhs x U by rewrite nbhsE /=; exists U.
rewrite -nbhs_ballE /nbhs_ball /nbhs_ball_ => -[_/posnumP[r] xrU].
have /rat_in_itvoo[q qxxr] : (x - r%:num < x + r%:num)%R.
  by rewrite ltrBlDr -addrA ltrDl.
exists q, `](x - r%:num)%R, (x + r%:num)%R[%classic; last first.
  by rewrite /= in_itv/= ltrBlDl ltrDr// ltrDl//; apply/andP.
split=> //; split; [exact: interval_open|exact: interval_is_interval|].
move=> y /=; rewrite in_itv/= => /andP[xy yxr]; apply xrU => /=.
rewrite /ball /= /ball_ /= in xrU *; have [yx|yx] := leP x y.
  by rewrite ler0_norm ?subr_le0// opprB ltrBlDl.
by rewrite gtr0_norm ?subr_gt0// ltrBlDr -ltrBlDl.
Qed.

End open_union_rat.

Lemma right_bounded_interior (R : realType) (X : set R) :
  has_ubound X -> X^° `<=` [set r | r < sup X].
Proof.
move=> uX r Xr; rewrite /mkset ltNge; apply/negP.
rewrite le_eqVlt => /orP[/eqP supXr|]; last first.
  by apply/negP; rewrite -leNgt sup_ubound//; exact: interior_subset.
suff : ~ X^° (sup X) by rewrite supXr.
case/nbhs_ballP => _/posnumP[e] supXeX.
have [f XsupXf] : exists f : {posnum R}, X (sup X + f%:num).
  exists (e%:num / 2)%:pos; apply supXeX; rewrite /ball /= opprD addNKr normrN.
  by rewrite gtr0_norm // ltr_pdivrMr // ltr_pMr // ltr1n.
have : sup X + f%:num <= sup X by exact: sup_ubound.
by apply/negP; rewrite -ltNge; rewrite ltrDl.
Qed.

Lemma left_bounded_interior (R : realType) (X : set R) :
  has_lbound X -> X^° `<=` [set r | inf X < r].
Proof.
move=> lX r Xr; rewrite /mkset ltNge; apply/negP.
rewrite le_eqVlt => /orP[/eqP rinfX|]; last first.
  by apply/negP; rewrite -leNgt inf_lbound//; exact: interior_subset.
suff : ~ X^° (inf X) by rewrite -rinfX.
case/nbhs_ballP => _/posnumP[e] supXeX.
have [f XsupXf] : exists f : {posnum R}, X (inf X - f%:num).
  exists (e%:num / 2)%:pos; apply supXeX; rewrite /ball /= opprB addrC subrK.
  by rewrite gtr0_norm // ltr_pdivrMr // ltr_pMr // ltr1n.
have : inf X <= inf X - f%:num by exact: inf_lbound.
by apply/negP; rewrite -ltNge; rewrite ltrBlDr ltrDl.
Qed.

Lemma interval_unbounded_setT {R : realFieldType} (X : set R) : is_interval X ->
  ~ has_lbound X -> ~ has_ubound X -> X = setT.
Proof.
move=> iX lX uX; rewrite predeqE => x; split => // _.
move/has_lbPn : lX => /(_ x) [y Xy xy].
move/has_ubPn : uX => /(_ x) [z Xz xz].
by apply: (iX y z); rewrite ?ltW.
Qed.

Section interval_realType.
Variable R : realType.

Lemma interval_left_unbounded_interior (X : set R) : is_interval X ->
  ~ has_lbound X -> has_ubound X -> X^° = [set r | r < sup X].
Proof.
move=> iX lX uX; rewrite eqEsubset; split; first exact: right_bounded_interior.
rewrite -(open_subsetE _ (@open_lt _ _)) => r rsupX.
move/has_lbPn : lX => /(_ r)[y Xy yr].
have hsX : has_sup X by split => //; exists y.
have /sup_adherent/(_ hsX)[e Xe] : 0 < sup X - r by rewrite subr_gt0.
by rewrite subKr => re; apply: (iX y e); rewrite ?ltW.
Qed.

Lemma interval_right_unbounded_interior (X : set R) : is_interval X ->
  has_lbound X -> ~ has_ubound X -> X^° = [set r | inf X < r].
Proof.
move=> iX lX uX; rewrite eqEsubset; split; first exact: left_bounded_interior.
rewrite -(open_subsetE _ (@open_gt _ _)) => r infXr.
move/has_ubPn : uX => /(_ r)[y Xy yr].
have hiX : has_inf X by split => //; exists y.
have /inf_adherent/(_ hiX)[e Xe] : 0 < r - inf X by rewrite subr_gt0.
by rewrite addrC subrK => er; apply: (iX e y); rewrite ?ltW.
Qed.

Lemma interval_bounded_interior (X : set R) : is_interval X ->
  has_lbound X -> has_ubound X -> X^° = [set r | inf X < r < sup X].
Proof.
move=> iX bX aX; rewrite eqEsubset; split=> [r Xr|].
  apply/andP; split;
    [exact: left_bounded_interior|exact: right_bounded_interior].
rewrite -open_subsetE; last exact: (@interval_open _ (BRight _) (BLeft _)).
move=> r /andP[iXr rsX].
have [X0|/set0P X0] := eqVneq X set0.
  by move: (lt_trans iXr rsX); rewrite X0 inf_out ?sup_out ?ltxx // => - [[]].
have hiX : has_inf X by split.
have /inf_adherent/(_ hiX)[e Xe] : 0 < r - inf X by rewrite subr_gt0.
rewrite addrC subrK => er.
have hsX : has_sup X by split.
have /sup_adherent/(_ hsX)[f Xf] : 0 < sup X - r by rewrite subr_gt0.
by rewrite subKr => rf; apply: (iX e f); rewrite ?ltW.
Qed.

Lemma interior_set1 (a : R) : [set a]^° = set0.
Proof.
rewrite interval_bounded_interior; first last.
- by exists a => [?]/= ->; apply: lexx.
- by exists a => [?]/= ->; apply: lexx.
- by move=> ? ?/= -> -> r; rewrite -eq_le; move/eqP <-.
- rewrite inf1 sup1 eqEsubset; split => // => x/=.
  by rewrite ltNge => /andP[/negP + ?]; apply; apply/ltW.
Qed.

Lemma interior_itv_bnd (x y : R) (a b : bool) :
  [set` Interval (BSide a x) (BSide b y)]^° = `]x, y[%classic.
Proof.
have [|xy] := leP y x.
  rewrite le_eqVlt => /predU1P[-> |yx].
    by case: a; case: b; rewrite set_itvoo0 ?set_itvE ?interior_set1 ?interior0.
  rewrite !set_itv_ge ?interior0//.
  - by rewrite bnd_simp -leNgt ltW.
  - by case: a; case: b; rewrite bnd_simp -?leNgt -?ltNge ?ltW.
rewrite interval_bounded_interior//; last exact: interval_is_interval.
rewrite inf_itv; last by case: a; case b; rewrite bnd_simp ?ltW.
rewrite sup_itv; last by case: a; case b; rewrite bnd_simp ?ltW.
exact: set_itvoo.
Qed.

Lemma interior_itv_bndy (x : R) (b : bool) :
  [set` Interval (BSide b x) (BInfty _ false)]^° = `]x, +oo[%classic.
Proof.
rewrite interval_right_unbounded_interior//; first last.
    by apply: hasNubound_itv; rewrite lt_eqF.
  exact: interval_is_interval.
rewrite inf_itv; last by case: b; rewrite bnd_simp ?ltW.
by rewrite set_itv_o_infty.
Qed.

Lemma interior_itv_Nybnd (y : R) (b : bool) :
  [set` Interval (BInfty _ true) (BSide b y)]^° = `]-oo, y[%classic.
Proof.
rewrite interval_left_unbounded_interior//; first last.
    by apply: hasNlbound_itv; rewrite gt_eqF.
  exact: interval_is_interval.
rewrite sup_itv; last by case b; rewrite bnd_simp ?ltW.
by apply: set_itv_infty_o.
Qed.

Lemma interior_itv_Nyy :
  [set` Interval (BInfty R true) (BInfty _ false)]^° = `]-oo, +oo[%classic.
Proof. by rewrite set_itv_infty_infty; apply: interiorT. Qed.

Definition interior_itv :=
  (interior_itv_bnd, interior_itv_bndy, interior_itv_Nybnd, interior_itv_Nyy).

Definition Rhull (X : set R) : interval R := Interval
  (if `[< has_lbound X >] then BSide `[< X (inf X) >] (inf X)
                          else BInfty _ true)
  (if `[< has_ubound X >] then BSide (~~ `[< X (sup X) >]) (sup X)
                          else BInfty _ false).

Lemma Rhull0 : Rhull set0 = `]0, 0[ :> interval R.
Proof.
rewrite /Rhull  (asboolT (has_lbound0 R)) (asboolT (has_ubound0 R)) asboolF //.
by rewrite sup0 inf0.
Qed.

Lemma sub_Rhull (X : set R) : X `<=` [set x | x \in Rhull X].
Proof.
move=> x Xx/=; rewrite in_itv/=.
case: (asboolP (has_lbound _)) => ?; case: (asboolP (has_ubound _)) => ? //=.
+ by case: asboolP => ?; case: asboolP => ? //=;
     rewrite !(lteifF,lteifT,sup_ubound,inf_lbound,sup_ub_strict,inf_lb_strict).
+ by case: asboolP => XinfX; rewrite !(lteifF, lteifT);
     [rewrite inf_lbound | rewrite inf_lb_strict].
+ by case: asboolP => XsupX; rewrite !(lteifF, lteifT);
     [rewrite sup_ubound | rewrite sup_ub_strict].
Qed.

Lemma is_intervalP (X : set R) : is_interval X <-> X = [set x | x \in Rhull X].
Proof.
split=> [iX|->]; last exact: interval_is_interval.
rewrite predeqE => x /=; split; [exact: sub_Rhull | rewrite in_itv/=].
case: (asboolP (has_lbound _)) => ?; case: (asboolP (has_ubound _)) => ? //=.
- case: asboolP => XinfX; case: asboolP => XsupX;
    rewrite !(lteifF, lteifT).
  + move=> /andP[]; rewrite le_eqVlt => /orP[/eqP <- //|infXx].
    rewrite le_eqVlt => /orP[/eqP -> //|xsupX].
    apply: (@interior_subset R).
    by rewrite interval_bounded_interior // /mkset infXx.
  + move=> /andP[]; rewrite le_eqVlt => /orP[/eqP <- //|infXx supXx].
    apply: (@interior_subset R).
    by rewrite interval_bounded_interior // /mkset infXx.
  + move=> /andP[infXx]; rewrite le_eqVlt => /orP[/eqP -> //|xsupX].
    apply: (@interior_subset R).
    by rewrite interval_bounded_interior // /mkset infXx.
  + move=> ?; apply: (@interior_subset R).
    by rewrite interval_bounded_interior // /mkset infXx.
- case: asboolP => XinfX; rewrite !(lteifF, lteifT, andbT).
  + rewrite le_eqVlt => /orP[/eqP<-//|infXx].
    apply: (@interior_subset R).
    by rewrite interval_right_unbounded_interior.
  + move=> infXx; apply: (@interior_subset R).
    by rewrite interval_right_unbounded_interior.
- case: asboolP => XsupX /=.
  + rewrite le_eqVlt => /orP[/eqP->//|xsupX].
    apply: (@interior_subset R).
    by rewrite interval_left_unbounded_interior.
  + move=> xsupX; apply: (@interior_subset R).
    by rewrite interval_left_unbounded_interior.
- by move=> _; rewrite (interval_unbounded_setT iX).
Qed.

Lemma connected_intervalP (E : set R) : connected E <-> is_interval E.
Proof.
split => [cE x y Ex Ey z /andP[xz zy]|].
- apply: contrapT => Ez.
  pose Az := E `&` [set x | x < z]; pose Bz := E `&` [set x | z < x].
  apply/connectedPn : cE; exists (fun b => if b then Az else Bz); split.
  + move: xz zy Ez.
    rewrite !le_eqVlt => /predU1P[<-//|xz] /predU1P[->//|zy] Ez.
    by case; [exists x | exists y].
  + rewrite /Az /Bz -setIUr; apply/esym/setIidPl => u Eu.
    by apply/orP; rewrite -neq_lt; apply/negP; apply: contraPnot Eu => /eqP <-.
  + split; [|rewrite setIC].
    + apply/disjoints_subset => /= u /closureI[_]; rewrite closure_gt => zu.
      by rewrite /Az setCI; right; apply/negP; rewrite -leNgt.
    + apply/disjoints_subset => /= u /closureI[_]; rewrite closure_lt => zu.
      by rewrite /Bz setCI; right; apply/negP; rewrite -leNgt.
- apply: contraPP => /connectedPn[A [A0 EU sepA]] intE.
  have [/= x A0x] := A0 false; have [/= y A1y] := A0 true.
  wlog xy : A A0 EU sepA x A0x y A1y / x < y.
    move=> /= wlog_hypo; have [xy|yx|{wlog_hypo}yx] := ltgtP x y.
    + exact: (wlog_hypo _ _ _ _ _ A0x _ A1y).
    + apply: (wlog_hypo (A \o negb) _ _ _ y _ x) => //=;
      by [rewrite setUC | rewrite separatedC].
    + move/separated_disjoint : sepA; rewrite predeqE => /(_ x)[] + _; apply.
      by split => //; rewrite yx.
  pose z := sup (A false `&` [set z | x <= z <= y]).
  have A1z : ~ (A true) z.
    have cA0z : closure (A false) z.
      suff : closure (A false `&` [set z | x <= z <= y]) z by case/closureI.
      apply: closure_sup; last by exists y => u [_] /andP[].
      by exists x; split => //; rewrite /mkset lexx /= (ltW xy).
    by move: sepA; rewrite /separated => -[] /disjoints_subset + _; apply.
  have /andP[xz zy] : x <= z < y.
    rewrite sup_ubound//=; [|by exists y => u [_] /andP[]|].
    + rewrite lt_neqAle sup_le_ub ?andbT; last by move=> u [_] /andP[].
      * by apply/negP; apply: contraPnot A1y => /eqP <-.
      * by exists x; split => //; rewrite /mkset /= lexx /= (ltW xy).
    + by split=> //; rewrite /mkset lexx (ltW xy).
  have [A0z|A0z] := pselect ((A false) z); last first.
  have {}xzy : x <= z <= y by rewrite xz ltW.
    have : ~ E z by rewrite EU => -[].
    by apply; apply (intE x y) => //; rewrite EU; [left|right].
  suff [z1 [/andP[zz1 z1y] Ez1]] : exists z1 : R, z <= z1 <= y /\ ~ E z1.
    apply Ez1; apply (intE x y) => //; rewrite ?EU; [by left|by right|].
    by rewrite z1y (le_trans _ zz1).
  have [r zcA1] : {r:{posnum R}| ball z r%:num `<=` ~` closure (A true)}.
    have ? : ~ closure (A true) z.
      by move: sepA; rewrite /separated => -[] _ /disjoints_subset; apply.
    have ? : open (~` closure (A true)) by exact/closed_openC/closed_closure.
    exact/nbhsC_ball/open_nbhs_nbhs.
  pose z1 : R := z + r%:num / 2; exists z1.
  have z1y : z1 <= y.
    rewrite leNgt; apply/negP => yz1.
    suff : (~` closure (A true)) y by apply; exact: subset_closure.
    apply zcA1; rewrite /ball /= ltr_distl (lt_le_trans zy) // ?lerDl //.
    rewrite andbT ltrBlDl addrC (lt_trans yz1) // ltrD2l.
    by rewrite ltr_pdivrMr // ltr_pMr // ltr1n.
  rewrite z1y andbT lerDl; split => //.
  have ncA1z1 : (~` closure (A true)) z1.
    apply zcA1; rewrite /ball /= /z1 opprD addNKr normrN.
    by rewrite ger0_norm // ltr_pdivrMr // ltr_pMr // ltr1n.
  have nA0z1 : ~ (A false) z1.
    move=> A0z1; have : z < z1 by rewrite /z1 ltrDl.
    apply/negP; rewrite -leNgt.
     apply: sup_ubound; first by exists y => u [_] /andP[].
    by split => //; rewrite /mkset /z1 (le_trans xz) /= ?lerDl // (ltW z1y).
  by rewrite EU => -[//|]; apply: contra_not ncA1z1; exact: subset_closure.
Qed.
End interval_realType.

Section segment.
Variable R : realType.

(** properties of segments in R *)

Lemma segment_connected (a b : R) : connected `[a, b].
Proof. exact/connected_intervalP/interval_is_interval. Qed.

Lemma segment_compact (a b : R) : compact `[a, b].
Proof.
have [leab|ltba] := lerP a b; last first.
  by move=> F FF /filter_ex [x abx]; move: ltba; rewrite (itvP abx).
rewrite compact_cover => I D f fop sabUf.
set B := [set x | exists2 E : {fset I}, {subset E <= D} &
  `[a, x] `<=` \bigcup_(i in [set` E]) f i /\ (\bigcup_(i in [set` E]) f i) x].
set A := `[a, b] `&` B.
suff Aeab : A = `[a, b]%classic.
  suff [_ [E ? []]] : A b by exists E.
  by rewrite Aeab/= inE/=; exact/andP.
apply: segment_connected.
- have aba : a \in `[a, b] by rewrite in_itv /= lexx.
  exists a; split=> //; have /sabUf [i /= Di fia] := aba.
  exists [fset i]%fset; first by move=> ?; rewrite inE inE => /eqP->.
  split; last by exists i => //=; rewrite inE.
  move=> x /= aex; exists i; [by rewrite /= inE|suff /eqP-> : x == a by []].
  by rewrite eq_le !(itvP aex).
- exists B => //; rewrite openE => x [E sD [saxUf [i Di fx]]].
  have : open (f i) by have /sD := Di; rewrite inE => /fop.
  rewrite openE => /(_ _ fx) [e egt0 xe_fi]; exists e => // y xe_y.
  exists E => //; split; last by exists i => //; apply/xe_fi.
  move=> z /= ayz; have [lezx|ltxz] := lerP z x.
    by apply/saxUf; rewrite /= in_itv/= (itvP ayz) lezx.
  exists i => //; apply/xe_fi; rewrite /ball_/= distrC ger0_norm.
    have lezy : z <= y by rewrite (itvP ayz).
    rewrite ltrBlDl; apply: le_lt_trans lezy _; rewrite -ltrBlDr.
    by have := xe_y; rewrite /ball_ => /ltr_distlCBl.
  by rewrite subr_ge0; apply/ltW.
exists A; last by rewrite predeqE => x; split=> [[] | []].
move=> x clAx; have abx : x \in `[a, b].
  by apply: interval_closed; have /closureI [] := clAx.
split=> //; have /sabUf [i Di fx] := abx.
have /fop := Di; rewrite openE => /(_ _ fx) [_ /posnumP[e] xe_fi].
have /clAx [y [[aby [E sD [sayUf _]]] xe_y]] :=
  nbhsx_ballx x e%:num ltac:(by []).
exists (i |` E)%fset; first by move=> j /fset1UP[->|/sD] //; rewrite inE.
split=> [z axz|]; last first.
  exists i; first by rewrite /= !inE eq_refl.
  by apply/xe_fi; rewrite /ball_/= subrr normr0.
have [lezy|ltyz] := lerP z y.
  have /sayUf [j Dj fjz] : z \in `[a, y] by rewrite in_itv /= (itvP axz) lezy.
  by exists j => //=; rewrite inE orbC Dj.
exists i; first by rewrite /= !inE eq_refl.
apply/xe_fi; rewrite /ball_/= ger0_norm; last by rewrite subr_ge0 (itvP axz).
rewrite ltrBlDl -ltrBlDr; apply: lt_trans ltyz.
by apply: ltr_distlCBl; rewrite distrC.
Qed.

End segment.

Lemma IVT (R : realType) (f : R -> R) (a b v : R) :
  a <= b -> {within `[a, b], continuous f} ->
  minr (f a) (f b) <= v <= maxr (f a) (f b) ->
  exists2 c, c \in `[a, b] & f c = v.
Proof.
move=> leab fcont; gen have ivt : f v fcont / f a <= v <= f b ->
    exists2 c, c \in `[a, b] & f c = v; last first.
  case: (leP (f a) (f b)) => [] _ fabv /=; first exact: ivt.
  have [| |c cab /oppr_inj] := ivt (- f) (- v); last by exists c.
  - by move=> x /=; apply/continuousN/fcont.
  - by rewrite lerNr opprK lerNr opprK andbC.
move=> favfb; suff: is_interval (f @` `[a,b]).
  apply; last exact: favfb.
  - by exists a => //=; rewrite in_itv/= lexx.
  - by exists b => //=; rewrite in_itv/= leab lexx.
apply/connected_intervalP/connected_continuous_connected => //.
exact: segment_connected.
Qed.

(* Local properties in R *)

(* Topology on [R]² *)

(* Lemma locally_2d_align : *)
(*   forall (P Q : R -> R -> Prop) x y, *)
(*   ( forall eps : {posnum R}, (forall uv, ball (x, y) eps uv -> P uv.1 uv.2) -> *)
(*     forall uv, ball (x, y) eps uv -> Q uv.1 uv.2 ) -> *)
(*   {near x & y, forall x y, P x y} ->  *)
(*   {near x & y, forall x y, Q x y}. *)
(* Proof. *)
(* move=> P Q x y /= K => /locallyP [d _ H]. *)
(* apply/locallyP; exists d => // uv Huv. *)
(* by apply (K d) => //. *)
(* Qed. *)

(* Lemma locally_2d_1d_const_x : *)
(*   forall (P : R -> R -> Prop) x y, *)
(*   locally_2d x y P -> *)
(*   locally y (fun t => P x t). *)
(* Proof. *)
(* move=> P x y /locallyP [d _ Hd]. *)
(* exists d => // z Hz. *)
(* by apply (Hd (x, z)). *)
(* Qed. *)

(* Lemma locally_2d_1d_const_y : *)
(*   forall (P : R -> R -> Prop) x y, *)
(*   locally_2d x y P -> *)
(*   locally x (fun t => P t y). *)
(* Proof. *)
(* move=> P x y /locallyP [d _ Hd]. *)
(* apply/locallyP; exists d => // z Hz. *)
(* by apply (Hd (z, y)). *)
(* Qed. *)

(* Lemma locally_2d_1d_strong (P : R -> R -> Prop) (x y : R): *)
(*   (\near x & y, P x y) -> *)
(*   \forall u \near x & v \near y, *)
(*       forall (t : R), 0 <= t <= 1 -> *)
(*       \forall z \near t, \forall a \near (x + z * (u - x)) *)
(*                                & b \near (y + z * (v - y)), P a b. *)
(* Proof. *)
(* move=> P x y. *)
(* apply locally_2d_align => eps HP uv Huv t Ht. *)
(* set u := uv.1. set v := uv.2. *)
(* have Zm : 0 <= Num.max `|u - x| `|v - y| by rewrite ler_maxr 2!normr_ge0. *)
(* rewrite ler_eqVlt in Zm. *)
(* case/orP : Zm => Zm. *)
(* - apply filterE => z. *)
(*   apply/locallyP. *)
(*   exists eps => // pq. *)
(*   rewrite !(RminusE,RmultE,RplusE). *)
(*   move: (Zm). *)
(*   have : Num.max `|u - x| `|v - y| <= 0 by rewrite -(eqP Zm). *)
(*   rewrite ler_maxl => /andP[H1 H2] _. *)
(*   rewrite (_ : u - x = 0); last by apply/eqP; rewrite -normr_le0. *)
(*   rewrite (_ : v - y = 0); last by apply/eqP; rewrite -normr_le0. *)
(*   rewrite !(mulr0,addr0); by apply HP. *)
(* - have : Num.max (`|u - x|) (`|v - y|) < eps. *)
(*     rewrite ltr_maxl; apply/andP; split. *)
(*     - case: Huv => /sub_ball_abs /=; by rewrite mul1r absrB. *)
(*     - case: Huv => _ /sub_ball_abs /=; by rewrite mul1r absrB. *)
(*   rewrite -subr_gt0 => /RltP H1. *)
(*   set d1 := mk{posnum R} _ H1. *)
(*   have /RltP H2 : 0 < pos d1 / 2 / Num.max `|u - x| `|v - y| *)
(*     by rewrite mulr_gt0 // invr_gt0. *)
(*   set d2 := mk{posnum R} _ H2. *)
(*   exists d2 => // z Hz. *)
(*   apply/locallyP. *)
(*   exists [{posnum R} of d1 / 2] => //= pq Hpq. *)
(*   set p := pq.1. set q := pq.2. *)
(*   apply HP; split. *)
(*   + apply/sub_abs_ball => /=. *)
(*     rewrite absrB. *)
(*     rewrite (_ : p - x = p - (x + z * (u - x)) + (z - t + t) * (u - x)); last first. *)
(*       by rewrite subrK opprD addrA subrK. *)
(*     apply: (ler_lt_trans (ler_abs_add _ _)). *)
(*     rewrite (_ : pos eps = pos d1 / 2 + (pos eps - pos d1 / 2)); last first. *)
(*       by rewrite addrCA subrr addr0. *)
(*     rewrite (_ : pos eps - _ = d1) // in Hpq. *)
(*     case: Hpq => /sub_ball_abs Hp /sub_ball_abs Hq. *)
(*     rewrite mul1r /= (_ : pos eps - _ = d1) // !(RminusE,RplusE,RmultE,RdivE) // in Hp, Hq. *)
(*     rewrite absrB in Hp. rewrite absrB in Hq. *)
(*     rewrite (ltr_le_add Hp) // (ler_trans (absrM _ _)) //. *)
(*     apply (@ler_trans _ ((pos d2 + 1) * Num.max `|u - x| `|v - y|)). *)
(*     apply ler_pmul; [by rewrite normr_ge0 | by rewrite normr_ge0 | | ]. *)
(*     rewrite (ler_trans (ler_abs_add _ _)) // ler_add //. *)
(*     move/sub_ball_abs : Hz; rewrite mul1r => tzd2; by rewrite absrB ltrW. *)
(*     rewrite absRE ger0_norm //; by case/andP: Ht. *)
(*     by rewrite ler_maxr lerr. *)
(*     rewrite /d2 /d1 /=. *)
(*     set n := Num.max _ _. *)
(*     rewrite mulrDl mul1r -mulrA mulVr ?unitfE ?lt0r_neq0 // mulr1. *)
(*     rewrite ler_sub_addr addrAC -mulrDl -mulr2n -mulr_natr. *)
(*     by rewrite -mulrA mulrV ?mulr1 ?unitfE // subrK. *)
(*   + apply/sub_abs_ball => /=. *)
(*     rewrite absrB. *)
(*     rewrite (_ : (q - y) = (q - (y + z * (v - y)) + (z - t + t) * (v - y))); last first. *)
(*       by rewrite subrK opprD addrA subrK. *)
(*     apply: (ler_lt_trans (ler_abs_add _ _)). *)
(*     rewrite (_ : pos eps = pos d1 / 2 + (pos eps - pos d1 / 2)); last first. *)
(*       by rewrite addrCA subrr addr0. *)
(*     rewrite (_ : pos eps - _ = d1) // in Hpq. *)
(*     case: Hpq => /sub_ball_abs Hp /sub_ball_abs Hq. *)
(*     rewrite mul1r /= (_ : pos eps - _ = d1) // !(RminusE,RplusE,RmultE,RdivE) // in Hp, Hq. *)
(*     rewrite absrB in Hp. rewrite absrB in Hq. *)
(*     rewrite (ltr_le_add Hq) // (ler_trans (absrM _ _)) //. *)
(*     rewrite (@ler_trans _ ((pos d2 + 1) * Num.max `|u - x| `|v - y|)) //. *)
(*     apply ler_pmul; [by rewrite normr_ge0 | by rewrite normr_ge0 | | ]. *)
(*     rewrite (ler_trans (ler_abs_add _ _)) // ler_add //. *)
(*     move/sub_ball_abs : Hz; rewrite mul1r => tzd2; by rewrite absrB ltrW. *)
(*     rewrite absRE ger0_norm //; by case/andP: Ht. *)
(*     by rewrite ler_maxr lerr orbT. *)
(*     rewrite /d2 /d1 /=. *)
(*     set n := Num.max _ _. *)
(*     rewrite mulrDl mul1r -mulrA mulVr ?unitfE ?lt0r_neq0 // mulr1. *)
(*     rewrite ler_sub_addr addrAC -mulrDl -mulr2n -mulr_natr. *)
(*     by rewrite -mulrA mulrV ?mulr1 ?unitfE // subrK. *)
(* Qed. *)
(* Admitted. *)

(* TODO redo *)
(* Lemma locally_2d_1d (P : R -> R -> Prop) x y : *)
(*   locally_2d x y P -> *)
(*   locally_2d x y (fun u v => forall t, 0 <= t <= 1 -> locally_2d (x + t * (u - x)) (y + t * (v - y)) P). *)
(* Proof. *)
(* move/locally_2d_1d_strong. *)
(* apply: locally_2d_impl. *)
(* apply locally_2d_forall => u v H t Ht. *)
(* specialize (H t Ht). *)
(* have : locally t (fun z => locally_2d (x + z * (u - x)) (y + z * (v - y)) P) by []. *)
(* by apply: locally_singleton. *)
(* Qed. *)

(* TODO redo *)
(* Lemma locally_2d_ex_dec : *)
(*   forall P x y, *)
(*   (forall x y, P x y \/ ~P x y) -> *)
(*   locally_2d x y P -> *)
(*   {d : {posnum R} | forall u v, `|u - x| < d -> `|v - y| < d -> P u v}. *)
(* Proof. *)
(* move=> P x y P_dec H. *)
(* destruct (@locally_ex _ (x, y) (fun z => P (fst z) (snd z))) as [d Hd]. *)
(* - move: H => /locallyP [e _ H]. *)
(*   by apply/locallyP; exists e. *)
(* exists d=>  u v Hu Hv. *)
(* by apply (Hd (u, v)) => /=; split; apply sub_abs_ball; rewrite absrB. *)
(* Qed. *)

Lemma compact_bounded (K : realType) (V : normedModType K) (A : set V) :
  compact A -> bounded_set A.
Proof.
rewrite compact_cover => Aco.
have covA : A `<=` \bigcup_(n : int) [set p | `|p| < n%:~R].
  by move=> p _; exists (floor `|p| + 1) => //=; rewrite lt_succ_floor.
have /Aco [] := covA.
  move=> n _; rewrite openE => p; rewrite /= -subr_gt0 => ltpn.
  apply/nbhs_ballP; exists (n%:~R - `|p|) => // q.
  rewrite -ball_normE /= ltrBrDr distrC; apply: le_lt_trans.
  by rewrite -{1}(subrK p q) ler_normD.
move=> D _ DcovA.
exists (\big[maxr/0]_(i : D) (fsval i)%:~R).
rewrite bigmax_real//; last by move=> ? _; rewrite realz.
split => // x ltmaxx p /DcovA [n Dn /lt_trans /(_ _)/ltW].
apply; apply: le_lt_trans ltmaxx.
have : n \in enum_fset D by [].
by rewrite enum_fsetE => /mapP[/= i iD ->]; exact/le_bigmax.
Qed.

Lemma rV_compact (T : ptopologicalType) n (A : 'I_n.+1 -> set T) :
  (forall i, compact (A i)) ->
  compact [ set v : 'rV[T]_n.+1 | forall i, A i (v ord0 i)].
Proof.
move=> Aico.
have : @compact (prod_topology _) [set f | forall i, A i (f i)].
  by apply: tychonoff.
move=> Aco F FF FA.
set G := [set [set f : 'I_n.+1 -> T | B (\row_j f j)] | B in F].
have row_simpl (v : 'rV[T]_n.+1) : \row_j (v ord0 j) = v.
  by apply/rowP => ?; rewrite mxE.
have row_simpl' (f : 'I_n.+1 -> T) : (\row_j f j) ord0 = f.
  by rewrite funeqE=> ?; rewrite mxE.
have [f [Af clGf]] : [set f | forall i, A i (f i)] `&`
  @cluster (prod_topology _) G !=set0.
  suff GF : ProperFilter G.
    apply: Aco; exists [set v : 'rV[T]_n.+1 | forall i, A i (v ord0 i)] => //.
    by rewrite predeqE => f; split => Af i; [have := Af i|]; rewrite row_simpl'.
  apply Build_ProperFilter_ex.
    move=> _ [C FC <-]; have /filter_ex [v Cv] := FC.
    by exists (v ord0); rewrite /= row_simpl.
  split.
  - by exists setT => //; apply: filterT.
  - by move=> _ _ [C FC <-] [D FD <-]; exists (C `&` D) => //; apply: filterI.
  move=> C D sCD [E FE EeqC]; exists [set v : 'rV[T]_n.+1 | D (v ord0)].
    by apply: filterS FE => v Ev; apply/sCD; rewrite -EeqC/= row_simpl.
  by rewrite predeqE => ? /=; rewrite row_simpl'.
exists (\row_j f j); split; first by move=> i; rewrite mxE; apply: Af.
move=> C D FC f_D; have {}f_D :
  nbhs (f : prod_topology _) [set g | D (\row_j g j)].
  have [E f_E sED] := f_D; rewrite nbhsE.
  set Pj := fun j Bj => open_nbhs (f j) Bj /\ Bj `<=` E ord0 j.
  have exPj : forall j, exists Bj, open_nbhs (f j) Bj /\ Bj `<=` E ord0 j.
    move=> j; have := f_E ord0 j; rewrite nbhsE => - [Bj].
    by rewrite row_simpl'; exists Bj.
  exists [set g | forall j, (get (Pj j)) (g j)]; last first.
    move=> g Pg; apply: sED => i j; rewrite ord1 row_simpl'.
    by have /getPex [_ /(_ _ (Pg j))] := exPj j.
  split; last by move=> j; have /getPex [[]] := exPj j.
  exists [set [set g | forall j, get (Pj j) (g j)] | k in [set x | 'I_n.+1 x]];
    last first.
    rewrite predeqE => g; split; first by move=> [_ [_ _ <-]].
    move=> Pg; exists [set g | forall j, get (Pj j) (g j)] => //.
    by exists ord0.
  move=> _ [_ _ <-]; set s := [seq (@^~ j) @^-1` (get (Pj j)) | j : 'I_n.+1].
  exists [fset x in s]%fset.
    move=> B'; rewrite in_fset => /mapP [j _ ->]; rewrite inE.
    exists j => //; exists (get (Pj j)) => //.
    by have /getPex [[]] := exPj j.
  rewrite predeqE => g; split=> [Ig j|Ig B'].
    apply: (Ig ((@^~ j) @^-1` (get (Pj j)))).
    by rewrite /= in_fset; apply/mapP; exists j => //; rewrite mem_enum.
  by rewrite /= in_fset => /mapP [j _ ->]; apply: Ig.
have GC : G [set g | C (\row_j g j)] by exists C.
by have [g []] := clGf _ _ GC f_D; exists (\row_j (g j : T)).
Qed.

Lemma bounded_closed_compact (R : realType) n (A : set 'rV[R]_n.+1) :
  bounded_set A -> closed A -> compact A.
Proof.
move=> [M [Mreal normAltM]] Acl.
have Mnco : compact
  [set v : 'rV[R]_n.+1 | forall i, v ord0 i \in `[(- (M + 1)), (M + 1)]].
  apply: (@rV_compact _  _ (fun _ => `[(- (M + 1)), (M + 1)]%classic)).
  by move=> _; apply: segment_compact.
apply: subclosed_compact Acl Mnco _ => v /normAltM normvleM i.
suff : `|v ord0 i : R| <= M + 1 by rewrite ler_norml.
apply: le_trans (normvleM _ _); last by rewrite ltrDl.
have /mapP[j Hj ->] : `|v ord0 i| \in [seq `|v x.1 x.2| | x : 'I_1 * 'I_n.+1].
  by apply/mapP; exists (ord0, i) => //=; rewrite mem_enum.
by rewrite [leRHS]/normr /= mx_normrE; apply/bigmax_geP; right => /=; exists j.
Qed.

(** Some limits on real functions *)

Section Shift.

Context {R : zmodType} {T : Type}.

Definition shift (x y : R) := y + x.
Notation center c := (shift (- c)).
Arguments shift x / y.

Lemma comp_shiftK (x : R) (f : R -> T) : (f \o shift x) \o center x = f.
Proof. by rewrite funeqE => y /=; rewrite addrNK. Qed.

Lemma comp_centerK (x : R) (f : R -> T) : (f \o center x) \o shift x = f.
Proof. by rewrite funeqE => y /=; rewrite addrK. Qed.

Lemma shift0 : shift 0 = id.
Proof. by rewrite funeqE => x /=; rewrite addr0. Qed.

Lemma center0 : center 0 = id.
Proof. by rewrite oppr0 shift0. Qed.

End Shift.
Arguments shift {R} x / y.
Notation center c := (shift (- c)).

Lemma near_shift {K : numDomainType} {R : normedModType K}
   (y x : R) (P : set R) :
   (\near x, P x) = (\forall z \near y, (P \o shift (x - y)) z).
Proof.
(* rewrite propeqE nbhs0P [X in _ <-> X]nbhs0P/= -propeqE. *)
(* by apply: eq_near => e; rewrite ![_ + e]addrC addrACA subrr addr0. *)
rewrite propeqE; split=> /= /nbhs_normP [_/posnumP[e] ye];
apply/nbhs_normP; exists e%:num => //= t et.
  by apply: ye; rewrite /= distrC addrCA [x + _]addrC addrK distrC.
by have /= := ye (t - (x - y)); rewrite opprB addrCA subrKA addrNK; exact.
Qed.

Lemma cvg_comp_shift {T : Type} {K : numDomainType} {R : normedModType K}
  (x y : R) (f : R -> T) :
  (f \o shift x) @ y = f @ (y + x).
Proof.
rewrite funeqE => A; rewrite /= !near_simpl (near_shift (y + x)).
by rewrite (_ : _ \o _ = A \o f) // funeqE=> z; rewrite /= opprD addNKr addrNK.
Qed.

Section continuous.
Variables (K : numFieldType) (U V : normedModType K).

Lemma continuous_shift (f : U -> V) u :
  {for u, continuous f} = {for 0, continuous (f \o shift u)}.
Proof.
by rewrite [in RHS]forE /continuous_at/= add0r cvg_comp_shift add0r.
Qed.

Lemma continuous_withinNshiftx (f : U -> V) u :
  f \o shift u @ 0^' --> f u <-> {for u, continuous f}.
Proof.
rewrite continuous_shift; split=> [cfu|].
  by apply/(continuous_withinNx _ _).2/(cvg_trans cfu); rewrite /= add0r.
by move/(continuous_withinNx _ _).1/cvg_trans; apply; rewrite /= add0r.
Qed.

End continuous.

Section ball_realFieldType.
Variables (R : realFieldType).

Lemma ball0 (a r : R) : ball a r = set0 <-> r <= 0.
Proof.
split.
  move=> /seteqP[+ _] => H; rewrite leNgt; apply/negP => r0.
  by have /(_ (ballxx _ r0)) := H a.
move=> r0; apply/seteqP; split => // y; rewrite /ball/=.
by move/lt_le_trans => /(_ _ r0); rewrite normr_lt0.
Qed.

End ball_realFieldType.

Lemma ball_open (R : numDomainType) (V : normedModType R) (x : V) (r : R) :
  0 < r -> open (ball x r).
Proof.
rewrite openE -ball_normE /interior => r0 y /= Bxy; near=> z.
rewrite /= (le_lt_trans (ler_distD y _ _)) // addrC -ltrBrDr.
by near: z; apply: cvgr_dist_lt; rewrite // subr_gt0.
Unshelve. all: by end_near. Qed.

Lemma ball_open_nbhs (R : numDomainType) (V : normedModType R) (x : V) (r : R) :
  0 < r -> open_nbhs x (ball x r).
Proof. by move=> e0; split; [exact: ball_open|exact: ballxx]. Qed.

Section Closed_Ball.

Definition closed_ball_ (R : numDomainType) (V : zmodType) (norm : V -> R)
  (x : V) (e : R) := [set y | norm (x - y) <= e].

Lemma closed_closed_ball_ (R : realFieldType) (V : normedModType R)
  (x : V) (e : R) : closed (closed_ball_ normr x e).
Proof.
rewrite /closed_ball_ -/((normr \o (fun y => x - y)) @^-1` [set x | x <= e]).
apply: (closed_comp _ (@closed_le _ _)) => y _.
apply: (continuous_comp _ (@norm_continuous _ _ _)).
exact: (continuousB (@cst_continuous _ _ _ _)).
Qed.

Definition closed_ball (R : numDomainType) (V : pseudoMetricType R)
  (x : V) (e : R) := closure (ball x e).

Lemma closed_ball0 (R : realFieldType) (a r : R) :
  r <= 0 -> closed_ball a r = set0.
Proof.
move=> /ball0 r0; apply/seteqP; split => // y.
by rewrite /closed_ball r0 closure0.
Qed.

Lemma closed_ballxx (R : numDomainType) (V : pseudoMetricType R) (x : V)
  (e : R) : 0 < e -> closed_ball x e x.
Proof. by move=> ?; exact/subset_closure/ballxx. Qed.

Lemma closed_ballE (R : realFieldType) (V : normedModType R) (x : V)
  (r : R) : 0 < r -> closed_ball x r = closed_ball_ normr x r.
Proof.
move=> /posnumP[e]; rewrite eqEsubset; split => y.
  rewrite /closed_ball closureE; apply; split; first exact: closed_closed_ball_.
  by move=> z; rewrite -ball_normE; exact: ltW.
have [-> _|xy] := eqVneq x y; first exact: closed_ballxx.
rewrite /closed_ball closureE -ball_normE.
rewrite /closed_ball_ /= le_eqVlt.
move => /orP[/eqP xye B [Bc Be]|xye _ [_ /(_ _ xye)]//].
apply: Bc => B0 /nbhs_ballP[s s0] B0y.
have [es|se] := leP s e%:num; last first.
  exists x; split; first by apply: Be; rewrite ball_normE; apply: ballxx.
  by apply: B0y; rewrite -ball_normE /ball_ /= distrC xye.
exists (y + (s / 2) *: (`|x - y|^-1 *: (x - y))); split; [apply: Be|apply: B0y].
  rewrite /= opprD addrA -[X in `|X - _|](scale1r (x - y)) scalerA -scalerBl.
  rewrite -[X in X - _](@divrr _ `|x - y|) ?unitfE ?normr_eq0 ?subr_eq0//.
  rewrite -mulrBl -scalerA normrZ normfZV ?subr_eq0// mulr1.
  rewrite gtr0_norm; first by rewrite ltrBlDl xye ltrDr mulr_gt0.
  by rewrite subr_gt0 xye ltr_pdivrMr // mulr_natr mulr2n ltr_pwDl.
rewrite -ball_normE /ball_ /= opprD addrA addrN add0r normrN normrZ.
rewrite normfZV ?subr_eq0// mulr1 normrM (gtr0_norm s0) gtr0_norm //.
by rewrite ltr_pdivrMr // ltr_pMr // ltr1n.
Qed.

Lemma closed_ball_closed (R : realFieldType) (V : pseudoMetricType R) (x : V)
  (r : R) : closed (closed_ball x r).
Proof. exact: closed_closure. Qed.

Lemma closed_ball_itv (R : realFieldType) (x r : R) : 0 < r ->
  closed_ball x r = `[x - r, x + r]%classic.
Proof.
by move=> r0; apply/seteqP; split => y;
  rewrite closed_ballE// /closed_ball_ /= in_itv/= ler_distlC.
Qed.

Lemma closed_ball_ball {R : realFieldType} (x r : R) : 0 < r ->
  closed_ball x r = [set x - r] `|` ball x r `|` [set x + r].
Proof.
move=> r0; rewrite closed_ball_itv// -(@setU1itv _ _ _ (x - r)); last first.
  by rewrite bnd_simp lerBlDr -addrA lerDl ltW// addr_gt0.
rewrite -(@setUitv1 _ _ _ (x + r)); last first.
  by rewrite bnd_simp ltrBlDr -addrA ltrDl addr_gt0.
by rewrite ball_itv setUA.
Qed.

Lemma closed_ballR_compact (R : realType) (x e : R) : 0 < e ->
  compact (closed_ball x e).
Proof.
move=> e_gt0; have : compact `[x - e, x + e] by apply: segment_compact.
by rewrite closed_ballE//; under eq_set do rewrite in_itv -ler_distlC.
Qed.

Lemma closed_ball_subset (R : realFieldType) (M : normedModType R) (x : M)
  (r0 r1 : R) : 0 < r0 -> r0 < r1 -> closed_ball x r0 `<=` ball x r1.
Proof.
move=> r00 r01; rewrite (_ : r0 = (PosNum r00)%:num) // closed_ballE //.
by move=> m xm; rewrite -ball_normE /ball_ /= (le_lt_trans _ r01).
Qed.

Lemma nbhs_closedballP (R : realFieldType) (M : normedModType R) (B : set M)
  (x : M) : nbhs x B <-> exists r : {posnum R}, closed_ball x r%:num `<=` B.
Proof.
split=> [/nbhs_ballP[_/posnumP[r] xrB]|[e xeB]]; last first.
  apply/nbhs_ballP; exists e%:num => //=.
  exact: (subset_trans (@subset_closure _ _) xeB).
exists (r%:num / 2)%:itv.
apply: (subset_trans (closed_ball_subset _ _) xrB) => //=.
by rewrite lter_pdivrMr // ltr_pMr // ltr1n.
Qed.

Lemma subset_closed_ball (R : realFieldType) (V : pseudoMetricType R) (x : V)
  (r : R) : ball x r `<=` closed_ball x r.
Proof. exact: subset_closure. Qed.

Lemma open_subball {R : numFieldType} {M : normedModType R} (A : set M)
  (x : M) : open A -> A x -> \forall e \near 0^'+, ball x e `<=` A.
Proof.
move=> oA Ax; have /nbhsr0P/= : nbhs x A by exact/open_nbhs_nbhs.
apply: filterS => e xeA y exy; apply: xeA.
by rewrite -ball_normE/= in exy; exact: ltW.
Qed.

Lemma closed_disjoint_closed_ball {R : realFieldType} {M : normedModType R}
    (K : set M) z : closed K -> ~ K z ->
  \forall d \near 0^'+, closed_ball z d `&` K = set0.
Proof.
rewrite -openC => /open_subball /[apply]; move=> [e /= e0].
move=> /(_ (e / 2)) /= ; rewrite sub0r normrN gtr0_norm ?divr_gt0//.
rewrite ltr_pdivrMr// ltr_pMr// ltr1n => /(_ erefl isT).
move/subsets_disjoint; rewrite setCK => ze2K0.
exists (e / 2); first by rewrite /= divr_gt0.
move=> x /= + x0; rewrite sub0r normrN gtr0_norm// => xe.
by move: ze2K0; apply: subsetI_eq0 => //=; exact: closed_ball_subset.
Qed.

Lemma locally_compactR (R : realType) : locally_compact [set: R].
Proof.
move=> x _; rewrite withinET; exists (closed_ball x 1).
  by apply/nbhs_closedballP; exists 1%:pos.
by split; [apply: closed_ballR_compact | apply: closed_ball_closed].
Qed.

Lemma subset_closure_half (R : realFieldType) (V : pseudoMetricType R) (x : V)
  (r : R) : 0 < r -> closed_ball x (r / 2) `<=` ball x r.
Proof.
move:r => _/posnumP[r] z /(_ (ball z ((r%:num/2)%:pos)%:num)) [].
  exact: nbhsx_ballx.
by move=> y [+/ball_sym]; rewrite [t in ball x t z]splitr; apply: ball_triangle.
Qed.

Lemma le_closed_ball (R : numFieldType) (M : pseudoMetricNormedZmodType R)
  (x : M) (e1 e2 : R) : (e1 <= e2)%O -> closed_ball x e1 `<=` closed_ball x e2.
Proof. by rewrite /closed_ball => le; apply/closure_subset/le_ball. Qed.

Lemma interior_closed_ballE (R : realType) (V : normedModType R) (x : V)
  (r : R) : 0 < r -> (closed_ball x r)^° = ball x r.
Proof.
move=> r0; rewrite eqEsubset; split; last first.
  by rewrite -open_subsetE; [exact: subset_closure | exact: ball_open].
move=> /= t; rewrite closed_ballE // /interior /= -nbhs_ballE => [[]] s s0.
have [-> _|nxt] := eqVneq t x; first exact: ballxx.
near ((0 : R^o)^') => e; rewrite -ball_normE /closed_ball_ => tsxr.
pose z := t + `|e| *: (t - x); have /tsxr /= : `|t - z| < s.
  rewrite distrC addrAC subrr add0r normrZ normr_id.
  rewrite -ltr_pdivlMr ?(normr_gt0,subr_eq0) //.
  by near: e; apply/dnbhs0_lt; rewrite divr_gt0 // normr_gt0 subr_eq0.
rewrite /z opprD addrA -scalerN -{1}(scale1r (x - t)) opprB -scalerDl normrZ.
apply lt_le_trans; rewrite ltr_pMl; last by rewrite normr_gt0 subr_eq0 eq_sym.
by rewrite ger0_norm // ltrDl normr_gt0; near: e; exists 1 => /=.
Unshelve. all: by end_near. Qed.

Lemma open_nbhs_closed_ball (R : realType) (V : normedModType R) (x : V)
  (r : R) : 0 < r -> open_nbhs x (closed_ball x r)^°.
Proof.
move=> r0; split; first exact: open_interior.
by rewrite interior_closed_ballE //; exact: ballxx.
Qed.

End Closed_Ball.

(* multi-rule bound_in_itv already exists in interval.v, but we
  advocate that it should actually have the following statement.
  This does not expose the order between interval bounds. *)
Lemma bound_itvE (R : numDomainType) (a b : R) :
  ((a \in `[a, b]) = (a <= b)) *
  ((b \in `[a, b]) = (a <= b)) *
  ((a \in `[a, b[) = (a < b)) *
  ((b \in `]a, b]) = (a < b)) *
  (a \in `[a, +oo[) *
  (a \in `]-oo, a]).
Proof. by rewrite !(boundr_in_itv, boundl_in_itv). Qed.

Section near_in_itv.
Context {R : realFieldType} (a b : R).

Lemma near_in_itvoo :
  {in `]a, b[, forall y, \forall z \near y, z \in `]a, b[}.
Proof. exact: interval_open. Qed.

Lemma near_in_itvoy :
  {in `]a, +oo[, forall y, \forall z \near y, z \in `]a, +oo[}.
Proof. exact: interval_open. Qed.

Lemma near_in_itvNyo :
  {in `]-oo, b[, forall y, \forall z \near y, z \in `]-oo, b[}.
Proof. exact: interval_open. Qed.

End near_in_itv.
#[deprecated(since="mathcomp-analysis 1.7.0",
  note="use `near_in_itvoo` instead")]
Notation near_in_itv := near_in_itvoo (only parsing).

Lemma cvg_patch {R : realType} (f : R -> R^o) (a b : R) (x : R) : (a < b)%R ->
  x \in `]a, b[ ->
  f @ (x : subspace `[a, b]) --> f x ->
  (f \_ `[a, b] x) @[x --> x] --> f x.
Proof.
move=> ab xab xf; apply/cvgrPdist_lt => /= e e0.
move/cvgrPdist_lt : xf => /(_ e e0) xf.
near=> z.
rewrite patchE ifT//; last first.
  rewrite inE; apply: subset_itv_oo_cc.
  by near: z; exact: near_in_itvoo.
near: z.
rewrite /prop_near1 /nbhs/= /nbhs_subspace ifT// in xf; last first.
  by rewrite inE/=; exact: subset_itv_oo_cc xab.
case: xf => x0 /= x00 xf.
near=> z.
apply: xf => //=.
rewrite inE; apply: subset_itv_oo_cc.
by near: z; exact: near_in_itvoo.
Unshelve. all: by end_near. Qed.

Notation "f @`[ a , b ]" :=
  (`[minr (f a) (f b), maxr (f a) (f b)]) : ring_scope.
Notation "f @`[ a , b ]" :=
  (`[minr (f a) (f b), maxr (f a) (f b)]%classic) : classical_set_scope.
Notation "f @`] a , b [" :=
  (`](minr (f a) (f b)), (maxr (f a) (f b))[) : ring_scope.
Notation "f @`] a , b [" :=
  (`](minr (f a) (f b)), (maxr (f a) (f b))[%classic) : classical_set_scope.

Section image_interval.
Variable R : realDomainType.
Implicit Types (a b : R) (f : R -> R).

Lemma mono_mem_image_segment a b f : monotonous `[a, b] f ->
  {homo f : x / x \in `[a, b] >-> x \in f @`[a, b]}.
Proof.
move=> [fle|fge] x xab; have leab : a <= b by rewrite (itvP xab).
  have: f a <= f b by rewrite fle ?bound_itvE.
  by case: leP => // fafb _; rewrite in_itv/= !fle ?(itvP xab).
have: f a >= f b by rewrite fge ?bound_itvE.
by case: leP => // fafb _; rewrite in_itv/= !fge ?(itvP xab).
Qed.

Lemma mono_mem_image_itvoo a b f : monotonous `[a, b] f ->
  {homo f : x / x \in `]a, b[ >-> x \in f @`]a, b[}.
Proof.
move=> []/[dup] => [/leW_mono_in|/leW_nmono_in] flt fle x xab;
    have ltab : a < b by rewrite (itvP xab).
  have: f a <= f b by rewrite ?fle ?bound_itvE ?ltW.
  by case: leP => // fafb _; rewrite in_itv/= ?flt ?in_itv/= ?(itvP xab, lexx).
have: f a >= f b by rewrite fle ?bound_itvE ?ltW.
by case: leP => // fafb _; rewrite in_itv/= ?flt ?in_itv/= ?(itvP xab, lexx).
Qed.

Lemma mono_surj_image_segment a b f : a <= b ->
    monotonous `[a, b] f -> set_surj `[a, b] (f @`[a, b]) f ->
  f @` `[a, b] = f @`[a, b]%classic.
Proof.
move=> leab fmono; apply: surj_image_eq => _ /= [x xab <-];
exact: mono_mem_image_segment.
Qed.

Lemma inc_segment_image a b f : f a <= f b -> f @`[a, b] = `[f a, f b].
Proof. by case: ltrP. Qed.

Lemma dec_segment_image a b f : f b <= f a -> f @`[a, b] = `[f b, f a].
Proof. by case: ltrP. Qed.

Lemma inc_surj_image_segment a b f : a <= b ->
    {in `[a, b] &, {mono f : x y / x <= y}} ->
    set_surj `[a, b] `[f a, f b] f ->
  f @` `[a, b] = `[f a, f b]%classic.
Proof.
move=> leab fle f_surj; have fafb : f a <= f b by rewrite fle ?bound_itvE.
by rewrite mono_surj_image_segment ?inc_segment_image//; left.
Qed.

Lemma dec_surj_image_segment a b f : a <= b ->
    {in `[a, b] &, {mono f : x y /~ x <= y}} ->
    set_surj `[a, b] `[f b, f a] f ->
  f @` `[a, b] = `[f b, f a]%classic.
Proof.
move=> leab fge f_surj; have fafb : f b <= f a by rewrite fge ?bound_itvE.
by rewrite mono_surj_image_segment ?dec_segment_image//; right.
Qed.

Lemma inc_surj_image_segmentP a b f : a <= b ->
    {in `[a, b] &, {mono f : x y / x <= y}} ->
    set_surj `[a, b] `[f a, f b] f ->
  forall y, reflect (exists2 x, x \in `[a, b] & f x = y) (y \in `[f a, f b]).
Proof.
move=> /inc_surj_image_segment/[apply]/[apply]/predeqP + y => /(_ y) fab.
by apply/(equivP idP); symmetry.
Qed.

Lemma dec_surj_image_segmentP a b f : a <= b ->
    {in `[a, b] &, {mono f : x y /~ x <= y}} ->
    set_surj `[a, b] `[f b, f a] f ->
  forall y, reflect (exists2 x, x \in `[a, b] & f x = y) (y \in `[f b, f a]).
Proof.
move=> /dec_surj_image_segment/[apply]/[apply]/predeqP + y => /(_ y) fab.
by apply/(equivP idP); symmetry.
Qed.

Lemma mono_surj_image_segmentP a b f : a <= b ->
    monotonous `[a, b] f -> set_surj `[a, b] (f @`[a, b]) f ->
  forall y, reflect (exists2 x, x \in `[a, b] & f x = y) (y \in f @`[a, b]).
Proof.
move=> /mono_surj_image_segment/[apply]/[apply]/predeqP + y => /(_ y) fab.
by apply/(equivP idP); symmetry.
Qed.

End image_interval.

Section LinearContinuousBounded.
Variables (R : numFieldType) (V W : normedModType R).

Lemma linear_boundedP (f : {linear V -> W}) : bounded_near f (nbhs 0) <->
  \forall r \near +oo, forall x, `|f x| <= r * `|x|.
Proof.
split=> [|/pinfty_ex_gt0 [r r0 Bf]]; last first.
  apply/ex_bound; exists r; apply/nbhs_norm0P; exists 1 => //= x /=.
  by rewrite -(gtr_pMr _ r0) => /ltW; exact/le_trans/Bf.
rewrite /bounded_near => /pinfty_ex_gt0 [M M0 /nbhs_norm0P [_/posnumP[e] efM]].
near (0 : R)^'+ => d; near=> r => x.
have[->|x0] := eqVneq x 0; first by rewrite raddf0 !normr0 mulr0.
have nd0 : d / `|x| > 0 by rewrite divr_gt0 ?normr_gt0.
have: `|f (d / `|x| *: x)| <= M.
  by apply: efM => /=; rewrite normrZ gtr0_norm// divfK ?normr_eq0//.
rewrite linearZ/= normrZ gtr0_norm// -ler_pdivlMl//; move/le_trans; apply.
rewrite invfM invrK mulrAC ler_wpM2r//; near: r; apply: nbhs_pinfty_ge.
by rewrite rpredM// ?rpredV ?gtr0_real.
Unshelve. all: by end_near. Qed.

Lemma continuous_linear_bounded (x : V) (f : {linear V -> W}) :
  {for 0, continuous f} -> bounded_near f (nbhs x).
Proof.
rewrite /prop_for/continuous_at linear0 /bounded_near => f0.
near=> M; apply/nbhs0P.
near do rewrite /= linearD (le_trans (ler_normD _ _))// -lerBrDl.
by apply: cvgr0_norm_le; rewrite // subr_gt0.
Unshelve. all: by end_near. Qed.

Lemma bounded_linear_continuous (f : {linear V -> W}) :
  bounded_near f (nbhs (0 : V)) -> continuous f.
Proof.
move=> /linear_boundedP [y [yreal fr]] x; near +oo_R => r.
apply/(@cvgrPdist_lt _ _ _ (nbhs x)) => e e_gt0; near=> z; rewrite -linearB.
rewrite (le_lt_trans (fr r _ _))// -?ltr_pdivlMl//.
by near: z; apply: cvgr_dist_lt => //; rewrite mulrC divr_gt0.
Unshelve. all: by end_near. Qed.

Lemma continuousfor0_continuous (f : {linear V -> W}) :
  {for 0, continuous f} -> continuous f.
Proof. by move=> /continuous_linear_bounded/bounded_linear_continuous. Qed.

Lemma linear_bounded_continuous (f : {linear V -> W}) :
  bounded_near f (nbhs 0) <-> continuous f.
Proof.
split; first exact: bounded_linear_continuous.
by move=> /(_ 0); exact: continuous_linear_bounded.
Qed.

Lemma bounded_funP (f : {linear V -> W}) :
  (forall r, exists M, forall x, `|x| <= r -> `|f x| <= M) <->
  bounded_near f (nbhs (0 : V)).
Proof.
split => [/(_ 1) [M Bf]|/linear_boundedP fr y].
  apply/ex_bound; exists M; apply/nbhs_normP => /=; exists 1 => //= x /=.
  by rewrite sub0r normrN => x1; exact/Bf/ltW.
near +oo_R => r; exists (r * y) => x xe.
rewrite (@le_trans _ _ (r * `|x|)) //; first by move: {xe} x; near: r.
by rewrite ler_pM.
Unshelve. all: by end_near. Qed.

End LinearContinuousBounded.

Section center_radius.
Context {R : numDomainType} {M : pseudoPMetricType R}.
Implicit Types A : set M.

(* NB: the identifier "center" is already taken! *)
Definition cpoint A := get [set c | exists r, A = ball c r].

Definition radius A : {nonneg R} :=
  xget 0%:nng [set r | A = ball (cpoint A) r%:num].

Definition is_ball A := A == ball (cpoint A) (radius A)%:num.

Definition scale_ball (k : R) A :=
  if is_ball A then ball (cpoint A) (k * (radius A)%:num) else set0.

Local Notation "k *` B" := (scale_ball k B).

Lemma sub_scale_ball A k l : k <= l -> k *` A `<=` l *` A.
Proof.
move=> kl; rewrite /scale_ball; case: ifPn=> [Aball|_]; last exact: subset_refl.
by apply: le_ball; rewrite ler_wpM2r.
Qed.

Lemma scale_ball1 A : is_ball A -> 1 *` A = A.
Proof. by move=> Aball; rewrite /scale_ball Aball mul1r; move/eqP in Aball. Qed.

Lemma sub1_scale_ball A l : is_ball A -> A `<=` l.+1%:R *` A.
Proof. by move/scale_ball1 => {1}<-; apply: sub_scale_ball; rewrite ler1n. Qed.

End center_radius.
Notation "k *` B" := (scale_ball k B) : classical_set_scope.

Lemma scale_ball0 {R : realFieldType} (A : set R) r : (r <= 0)%R ->
  r *` A = set0.
Proof.
move=> r0; apply/seteqP; split => // x.
rewrite /scale_ball; case: ifPn => // ballA.
by rewrite ((ball0 _ _).2 _)// mulr_le0_ge0.
Qed.

Section center_radius_realFieldType.
Context {R : realFieldType}.
Implicit Types x y r s : R.

Let ball_inj_radius_gt0 x y r s : 0 < r -> ball x r = ball y s -> 0 < s.
Proof.
move=> r0 xrys; rewrite ltNge; apply/negP => /ball0 s0; move: xrys.
by rewrite s0 => /seteqP[+ _] => /(_ x); apply; exact: ballxx.
Qed.

Let ball_inj_center x y r s : 0 < r -> ball x r = ball y s -> x = y.
Proof.
move=> r0 xrys; have s0 := ball_inj_radius_gt0 r0 xrys.
apply/eqP/negPn/negP => xy.
wlog : x y r s xrys r0 s0 xy / x < y.
  move: xy; rewrite neq_lt => /orP[xy|yx].
    by move/(_ _ _ _ _ xrys); apply => //; rewrite lt_eqF.
  by move/esym : xrys => /[swap] /[apply]; apply => //; rewrite lt_eqF.
move=> {}xy; have [rs|sr] := ltP r s.
- suff : ~ ball x r (y + r).
    by apply; rewrite xrys /ball/= ltr_distlC !ltrD2l -ltr_norml gtr0_norm.
  by rewrite /ball/= ltr_distlC ltrD2r (ltNge y) (ltW xy) andbF.
- suff : ~ ball y s (x - r + minr ((y - x) / 2) r).
    apply; rewrite -xrys /ball/= ltr_distlC ltrDl lt_min r0 andbT.
    rewrite divr_gt0 ?subr_gt0//= addrAC ltrBlDl addrCA ler_ltD//.
    by rewrite gt_min ltrDl r0 orbT.
  have [yx2r|ryx2] := ltP ((y - x) / 2) r.
    rewrite /ball/= ltr_distlC => /andP[+ _]; rewrite -(@ltr_pM2l _ 2)//.
    rewrite !mulrDr mulrCA divff// mulr1 ltNge => /negP; apply.
    rewrite addrAC !addrA (addrC _ y) mulr_natl mulr2n addrA addrK.
    rewrite (mulr_natl y) mulr2n -!addrA lerD2l (lerD (ltW _))//.
    by rewrite ler_wpM2l// lerNl opprK.
  rewrite subrK /ball/= ltr_distlC => /andP[].
  rewrite ltrBlDl addrC -ltrBlDl -(@ltr_pM2r _ (2^-1))//.
  move=> /le_lt_trans => /(_ _ ryx2) /le_lt_trans => /(_ _ sr).
  by rewrite ltr_pMr// invf_gt1// ltNge ler1n.
Qed.

Let ball_inj_radius x y r s : 0 < r -> ball x r = ball y s -> r = s.
Proof.
move=> r0 xrys; have s0 := ball_inj_radius_gt0 r0 xrys.
move: (xrys); rewrite (ball_inj_center r0 xrys) => {}xrys.
apply/eqP/negPn/negP; rewrite neq_lt => /orP[rs|sr].
- suff : ball y s (y + r) by rewrite -xrys /ball/= ltr_distlC ltxx andbF.
  rewrite /ball/= ltr_distlC !ltrD2l rs andbT (lt_trans _ r0)//.
  by rewrite ltrNl oppr0 (lt_trans r0).
- suff : ball y r (y + s) by rewrite xrys /ball/= ltr_distlC ltxx andbF.
  rewrite /ball/= ltr_distlC !ltrD2l sr andbT (lt_trans _ s0)//.
  by rewrite ltrNl oppr0 (lt_trans s0).
Qed.

Lemma ball_inj x y r s : 0 < r -> ball x r = ball y s -> x = y /\ r = s.
Proof.
by move=> r0 xrys; split; [exact: (ball_inj_center r0 xrys)|
                           exact: (ball_inj_radius r0 xrys)].
Qed.

Lemma radius0 : radius (@set0 R) = 0%:nng :> {nonneg R}.
Proof.
rewrite /radius/=; case: xgetP => [r _ /= /esym/ball0 r0|]/=.
  by apply/val_inj/eqP; rewrite /= eq_le r0/=.
by move=> /(_ 0%:nng) /nesym /ball0.
Qed.

Lemma is_ball0 : is_ball (@set0 R).
Proof.
rewrite /is_ball; apply/eqP/seteqP; split => // x; rewrite radius0/=.
by rewrite (ball0 _ _).2.
Qed.

Lemma cpoint_ball x r : 0 < r -> cpoint (ball x r) = x.
Proof.
move=> r0; rewrite /cpoint; case: xgetP => [y _ [s] /(ball_inj r0)[]//|].
by move=> /(_ x)/forallNP/(_ r).
Qed.

Lemma radius_ball_num x r : 0 <= r -> (radius (ball x r))%:num = r.
Proof.
rewrite le_eqVlt => /orP[/eqP <-|r0]; first by rewrite (ball0 _ _).2// radius0.
rewrite /radius; case: xgetP => [y _ /(ball_inj r0)[]//|].
by move=> /(_ (NngNum (ltW r0)))/=; rewrite cpoint_ball.
Qed.

Lemma radius_ball x r (r0 : 0 <= r) : radius (ball x r) = NngNum r0.
Proof. by apply/val_inj => //=; rewrite radius_ball_num. Qed.

Lemma is_ballP (A : set R) x : is_ball A ->
  A x -> `|cpoint A - x| < (radius A)%:num.
Proof. by rewrite /is_ball => /eqP {1}-> /lt_le_trans; exact. Qed.

Lemma is_ball_ball x r : is_ball (ball x r).
Proof.
have [r0|/ball0 ->] := ltP 0 r; last exact: is_ball0.
by apply/eqP; rewrite cpoint_ball// (radius_ball _ (ltW r0)).
Qed.

Lemma scale_ball_set0 (k : R) : k *` set0 = set0 :> set R.
Proof. by rewrite /scale_ball is_ball0// radius0/= mulr0 ball0. Qed.

Lemma ballE (A : set R) : is_ball A -> A = ball (cpoint A) (radius A)%:num.
Proof.
move=> ballA; apply/seteqP; split => [x /is_ballP|x Ax]; first exact.
by move: ballA => /eqP ->.
Qed.

Lemma is_ball_closureP (A : set R) x : is_ball A ->
  closure A x -> `|cpoint A - x| <= (radius A)%:num.
Proof.
move=> ballP cAx.
have : closed_ball (cpoint A) (radius A)%:num x by rewrite /closed_ball -ballE.
by have [r0|r0] := ltP 0 (radius A)%:num; [rewrite closed_ballE|
                                           rewrite closed_ball0].
Qed.

Lemma is_ball_closure (A : set R) : is_ball A ->
  closure A = closed_ball (cpoint A) (radius A)%:num.
Proof. by move=> ballA; rewrite /closed_ball -ballE. Qed.

Lemma closure_ball (c r : R) : closure (ball c r) = closed_ball c r.
Proof.
have [r0|r0] := leP r 0.
  by rewrite closed_ball0// ((ball0 _ _).2 r0) closure0.
by rewrite (is_ball_closure (is_ball_ball _ _)) cpoint_ball// radius_ball ?ltW.
Qed.

Lemma scale_ballE k x r : 0 <= k -> k *` ball x r = ball x (k * r).
Proof.
move=> k0; have [r0|r0] := ltP 0 r.
  apply/seteqP; split => y.
    rewrite /scale_ball is_ball_ball//= cpoint_ball//.
    by rewrite (radius_ball_num _ (ltW _)).
  by rewrite /scale_ball is_ball_ball cpoint_ball// radius_ball_num// ltW.
rewrite ((ball0 _ _).2 r0) scale_ball_set0; apply/esym/ball0.
by rewrite mulr_ge0_le0.
Qed.

Lemma cpoint_scale_ball A (k : R) : 0 < k -> is_ball A -> 0 < (radius A)%:num ->
  cpoint (k *` A) = cpoint A :> R.
Proof.
move=> k0 ballA r0.
rewrite [in LHS](ballE ballA) (scale_ballE _ _ (ltW k0))// cpoint_ball//.
by rewrite mulr_gt0.
Qed.

Lemma radius_scale_ball (A : set R) (k : R) : 0 <= k -> is_ball A ->
  (radius (k *` A))%:num = k * (radius A)%:num.
Proof.
move=> k0 ballA.
by rewrite [in LHS](ballE ballA) (scale_ballE _ _ k0)// radius_ball// mulr_ge0.
Qed.

Lemma is_scale_ball (A : set R) (k : R) : is_ball A -> is_ball (k *` A).
Proof.
move=> Aball.
have [k0|k0] := leP 0 k.
  by rewrite (ballE Aball) (scale_ballE _ _ k0); exact: is_ball_ball.
rewrite (_ : _ *` _ = set0); first exact: is_ball0.
apply/seteqP; split => // x.
by rewrite /scale_ball Aball (ball0 _ _).2// nmulr_rle0.
Qed.

End center_radius_realFieldType.

Section vitali_lemma_finite.
Context {R : realType} {I : eqType}.
Variable (B : I -> set R).
Hypothesis is_ballB : forall i, is_ball (B i).
Hypothesis B_set0 : forall i, B i !=set0.

Lemma vitali_lemma_finite (s : seq I) :
  { D : seq I | [/\ uniq D,
    {subset D <= s}, trivIset [set` D] B &
    forall i, i \in s -> exists j, [/\ j \in D,
      B i `&` B j !=set0,
      radius (B j) >= radius (B i) &
      B i `<=` 3 *` B j] ] }.
Proof.
pose LE x y := radius (B x) <= radius (B y).
have LE_trans : transitive LE by move=> x y z; exact: le_trans.
wlog : s / sorted LE s.
  have : sorted LE (sort LE s) by apply: sort_sorted => x y; exact: le_total.
  move=> /[swap] /[apply] -[D [uD Ds trivIset_DB H]]; exists D; split => //.
  - by move=> x /Ds; rewrite mem_sort.
  - by move=> i; rewrite -(mem_sort LE) => /H.
elim: s => [_|i [/= _ _|j t]]; first by exists nil.
  exists [:: i]; split => //; first by rewrite set_cons1; exact: trivIset1.
  move=> _ /[1!inE] /eqP ->; exists i; split => //; first by rewrite mem_head.
  - by rewrite setIid; exact: B_set0.
  - exact: sub1_scale_ball.
rewrite /= => + /andP[ij jt] => /(_ jt)[u [uu ujt trivIset_uB H]].
have [K|] := pselect (forall j, j \in u -> B j `&` B i = set0).
  have [iu|iu] := boolP (i \in u).
    exists u; split => //.
    - by move=> x /ujt xjt; rewrite inE xjt orbT.
    - move=> k /[1!inE] /predU1P[->{k}|].
        exists i; split; [by []| |exact: lexx|].
          by rewrite setIid; exact: B_set0.
        exact: sub1_scale_ball.
      by move/H => [l [lu lk0 kl k3l]]; exists l; split => //; rewrite inE lu orbT.
  exists (i :: u); split => //.
  - by rewrite /= iu.
  - move=> x /[1!inE] /predU1P[->|]; first by rewrite mem_head.
    by move/ujt => xjt; rewrite in_cons xjt orbT.
  - move=> k l /= /[1!inE] /predU1P[->{k}|ku].
      by move=> /predU1P[->{j}//|js] /set0P; rewrite setIC K// eqxx.
    by move=> /predU1P[->{l} /set0P|lu]; [rewrite K// eqxx|exact: trivIset_uB].
  - move=> k /[1!inE] /predU1P[->{k}|].
      exists i; split; [by rewrite mem_head| |exact: lexx|].
        by rewrite setIid; exact: B_set0.
      exact: sub1_scale_ball.
    by move/H => [l [lu lk0 kl k3l]]; exists l; split => //; rewrite inE lu orbT.
move/existsNP/cid => [k /not_implyP[ku /eqP/set0P ki0]].
exists u; split => //.
  by move=> l /ujt /[!inE] /predU1P[->|->]; rewrite ?eqxx ?orbT.
move=> _ /[1!inE] /predU1P[->|/H//]; exists k; split; [exact: ku| | |].
- by rewrite setIC.
- apply: (le_trans ij); move/ujt : ku => /[1!inE] /predU1P[<-|kt].
    exact: lexx.
  by have /allP := order_path_min LE_trans jt; apply; exact: kt.
- case: ki0 => x [Bkx Bix] y => iy.
  rewrite (ballE (is_ballB k)) scale_ballE// /ball/=.
  rewrite -(subrK x y) -(addrC x) opprD addrA opprB.
  rewrite (le_lt_trans (ler_normD _ _))// -nat1r mulrDl mul1r mulr_natl.
  rewrite (ltrD (is_ballP (is_ballB k) _))// -(subrK (cpoint (B i)) y).
  rewrite -(addrC (cpoint (B i))) opprD addrA opprB.
  rewrite (le_lt_trans (ler_normD _ _))//.
  apply (@lt_le_trans _ _ ((radius (B j))%:num *+ 2)); last first.
    apply: ler_wMn2r; move/ujt : ku; rewrite inE => /predU1P[<-|kt].
      exact: lexx.
    by have /allP := order_path_min LE_trans jt; apply; exact: kt.
  rewrite mulr2n ltrD//.
    by rewrite distrC (lt_le_trans (is_ballP (is_ballB i) _)).
  by rewrite (lt_le_trans (is_ballP (is_ballB i) _)).
Qed.

Lemma vitali_lemma_finite_cover (s : seq I) :
  { D : seq I | [/\ uniq D, {subset D <= s},
    trivIset [set` D] B &
    cover [set` s] B `<=` cover [set` D] (scale_ball 3%:R \o B)] }.
Proof.
have [D [uD DV tD maxD]] := vitali_lemma_finite s.
exists D; split => // x [i Vi] cBix/=.
by have [j [Dj BiBj ij]] := maxD i Vi; move/(_ _ cBix) => ?; exists j.
Qed.

End vitali_lemma_finite.

Section vitali_collection_partition.
Context {R : realType} {I : eqType}.
Variables (B : I -> set R) (V : set I) (r : R).
Hypothesis is_ballB : forall i, is_ball (B i).
Hypothesis B_set0 : forall i, 0 < (radius (B i))%:num.

Definition vitali_collection_partition n :=
  [set i | V i /\ r / (2 ^ n.+1)%:R < (radius (B i))%:num <= r / (2 ^ n)%:R].

Hypothesis VBr : forall i, V i -> (radius (B i))%:num <= r.

Lemma vitali_collection_partition_ub_gt0 i : V i -> 0 < r.
Proof. by move=> Vi; rewrite (lt_le_trans _ (VBr Vi)). Qed.

Notation r_gt0 := vitali_collection_partition_ub_gt0.

Lemma ex_vitali_collection_partition i :
  V i -> exists n, vitali_collection_partition n i.
Proof.
move=> Vi; pose f := floor (r / (radius (B i))%:num).
have f_ge0 : 0 <= f by rewrite floor_ge0// divr_ge0// ltW// (r_gt0 Vi).
have [m /andP[mf fm]] := leq_ltn_expn `|f|.-1.
exists m; split => //; apply/andP; split => [{mf}|{fm}].
  rewrite -(@ler_nat R) in fm.
  rewrite ltr_pdivrMr// mulrC -ltr_pdivrMr// (lt_le_trans _ fm)//.
  rewrite (lt_le_trans (lt_succ_floor _))//= -/f intrD -natr1 lerD2r//.
  have [<-|f0] := eqVneq 0 f; first by rewrite /= ler0n.
  rewrite prednK//; last by rewrite absz_gt0 eq_sym.
  by rewrite natr_absz// ger0_norm.
move: m => [|m] in mf *; first by rewrite expn0 divr1 VBr.
rewrite -(@ler_nat R) in mf.
rewrite ler_pdivlMr// mulrC -ler_pdivlMr//.
have [f0|f0] := eqVneq 0 f.
  by move: mf; rewrite -f0 absz0 leNgt expnS ltr_nat leq_pmulr// expn_gt0.
rewrite (le_trans mf)// prednK//; last by rewrite absz_gt0 eq_sym.
by rewrite natr_absz// ger0_norm// ge_floor.
Qed.

Lemma cover_vitali_collection_partition :
  V = \bigcup_n vitali_collection_partition n.
Proof.
apply/seteqP; split => [|i [n _] []//].
by move=> i Vi; have [n Hn] := ex_vitali_collection_partition Vi; exists n.
Qed.

Lemma disjoint_vitali_collection_partition n m : n != m ->
  vitali_collection_partition n `&`
  vitali_collection_partition m = set0.
Proof.
move=> nm; wlog : n m nm / (n < m)%N.
  move=> wlg; move: nm; rewrite neq_lt => /orP[nm|mn].
    by rewrite wlg// lt_eqF.
  by rewrite setIC wlg// lt_eqF.
move=> {}nm; apply/seteqP; split => // i [] [Vi] /andP[rnB _] [_ /andP[_]].
move/(lt_le_trans rnB); rewrite ltr_pM2l//; last by rewrite (r_gt0 Vi).
rewrite ltf_pV2 ?posrE ?ltr0n ?expn_gt0// ltr_nat.
by move/ltn_pexp2l => /(_ isT); rewrite ltnNge => /negP; apply.
Qed.

End vitali_collection_partition.

Lemma separated_closed_ball_countable
    {R : realType} (I : Type) (B : I -> set R) (D : set I) :
  (forall i, (radius (B i))%:num > 0) ->
  trivIset D (fun i => closed_ball (cpoint (B i)) (radius (B i))%:num) -> countable D.
Proof.
move=> B0 tD.
have : trivIset D (fun i => ball (cpoint (B i)) (radius (B i))%:num).
  move=> i j Di Dj BiBj; apply: tD => //.
  by apply: subsetI_neq0 BiBj => //; exact: subset_closed_ball.
apply: separated_open_countable => //; first by move=> i; exact: ball_open.
by move=> i; eexists; exact: ballxx.
Qed.

Section vitali_lemma_infinite.
Context {R : realType} {I : eqType}.
Variables (B : I -> set R) (V : set I) (r : R).
Hypothesis is_ballB : forall i, is_ball (B i).
Hypothesis Bset0 : forall i, (radius (B i))%:num > 0.
Hypothesis VBr : forall i, V i -> (radius (B i))%:num <= r.

Let B_ := vitali_collection_partition B V r.

Let H_ n (U : set I) := [set i | B_ n i /\
  forall j, U j -> i != j -> closure (B i) `&` closure (B j) = set0].

Let elt_prop (x : set I * nat * set I) :=
  x.1.1 `<=` V /\
  maximal_disjoint_subcollection (closure \o B) x.1.1 (H_ x.1.2 x.2).

Let elt_type := {x | elt_prop x}.

Let Rel (x y : elt_type) :=
  (sval y).2 = (sval x).2 `|` (sval x).1.1 /\ (sval x).1.2.+1 = (sval y).1.2.

Lemma vitali_lemma_infinite : { D : set I | [/\ countable D,
  D `<=` V, trivIset D (closure \o B) &
  forall i, V i -> exists j, [/\ D j,
    closure (B i) `&` closure (B j) !=set0,
    (radius (B j))%:num >= (radius (B i))%:num / 2 &
    closure (B i) `<=` closure (5%:R *` B j)] ] }.
Proof.
have [D0 [D0B0 tD0 maxD0]] :=
  ex_maximal_disjoint_subcollection (closure \o B) (B_ O).
have H0 : elt_prop (D0, 0%N, set0).
  split; first by move=> i /D0B0[].
  split => //=.
  - move=> x /= D0x; split; first exact: D0B0.
    by move=> s D0s xs; move/trivIsetP : tD0; exact.
  - by move=> F D0F FH0; apply: maxD0 => // i Fi; exact: (FH0 _ Fi).1.
have [v [Hv0 HvRel]] : {v : nat -> elt_type |
    v 0%N = exist _ _ H0 /\ forall n, Rel (v n) (v n.+1)}.
  apply: dependent_choice_Type => -[[[Dn n] Un] Hn].
  pose Hn1 := H_ n.+1 (Un `|` Dn).
  have [Dn1 maxDn1] :=
    ex_maximal_disjoint_subcollection (closure\o B) Hn1.
  suff: elt_prop (Dn1, n.+1, Un `|` Dn) by move=> H; exists (exist _ _ H).
  by split => //=; case: maxDn1 => + _ _ => /subset_trans; apply => i [[]].
pose D i := (sval (v i)).1.1.
pose U i := (sval (v i)).2.
have UE n : U n = \bigcup_(i < n) D i.
  elim: n => [|n ih]; first by rewrite bigcup_mkord big_ord0 /U /sval /D Hv0.
  by rewrite /U /sval/= (HvRel n).1 bigcup_mkord big_ord_recr -bigcup_mkord -ih.
pose v_ i := (sval (v i)).1.2.
have v_E n : v_ n = n.
  elim: n => /= [|n]; first by rewrite /v_ /sval/= Hv0.
  by move: (HvRel n).2; rewrite -!/(v_ _) => <- ->.
have maxD m : maximal_disjoint_subcollection (closure\o B) (D m)
    (H_ m (\bigcup_(i < m) D i)).
  by rewrite -(UE m) -[m in H_ m _]v_E /v_ /U /D; move: (v m) => [x []].
have DH m : D m `<=` H_ m (\bigcup_(i < m) D i) by have [] := maxD m.
exists (\bigcup_k D k); split.
- apply: bigcup_countable => // n _.
  apply: (@separated_closed_ball_countable R _ B) => //.
  have [_ + _] := maxD n; move=> DB i j Dni Dnj.
  by rewrite -!is_ball_closure//; exact: DB.
- by move=> i [n _ Dni]; have [+ _ _] := maxD n; move/(_ _ Dni) => [[]].
- apply: trivIset_bigcup => m; first by have [] := maxD m.
  move=> n i j mn Dmi Dnj.
  wlog : i j n m mn Dmi Dnj / (m < n)%N.
    move=> wlg ij.
    move: mn; rewrite neq_lt => /orP[mn|nm].
      by rewrite (wlg i j n m)// ?lt_eqF.
    by rewrite (wlg j i m n)// ?lt_eqF// setIC.
  move=> {}mn.
  have [_ {}H] := DH _ _ Dnj.
  move=> /set0P/eqP; apply: contra_notP => /eqP.
  by rewrite eq_sym setIC; apply: H => //; exists m.
move=> i Vi.
have [n Bni] := ex_vitali_collection_partition Bset0 VBr Vi.
have [[j Dj BiBj]|] :=
    pselect (exists2 j, (\bigcup_(i < n.+1) D i) j &
             closure (B i) `&` closure (B j) !=set0); last first.
  move/forall2NP => H.
  have {}H j : (\bigcup_(i < n.+1) D i) j ->
               closure (B i) `&` closure (B j) = set0.
    by have [//|/set0P/negP/negPn/eqP] := H j.
  have H_i : (H_ n (\bigcup_(i < n) D i)) i.
    split => // s Hs si; apply: H => //.
    by move: Hs => [m /= nm Dms]; exists m => //=; rewrite (ltn_trans nm).
  have Dn_Bi j : D n j -> closure (B i) `&` closure (B j) = set0.
    by move=> Dnj; apply: H; exists n => //=.
  have [Dni|Dni] := pselect (D n i).
    have := Dn_Bi _ Dni.
      rewrite setIid => /closure_eq0 Bi0.
      by have := Bset0 i; rewrite Bi0 radius0/= ltxx.
  have not_tB : ~ trivIset (D n `|` [set i]) (closure \o B).
    have [_ _] := maxD n.
    apply.
      split; first exact: subsetUl.
      by move=> x; apply/Dni; apply: x; right.
    by rewrite subUset; split; [exact: DH|]; rewrite sub1set inE.
  have [p [q [pq Dnpi Dnqi pq0]]] : exists p q, [/\ p != q,
      D n p \/ p = i, D n q \/ q = i &
      closure (B p) `&` closure (B q) !=set0].
    move/trivIsetP : not_tB => /existsNP[p not_tB]; exists p.
    move/existsNP : not_tB => [q not_tB]; exists q.
    move/not_implyP : not_tB => [Dnip] /not_implyP[Dni1] /not_implyP[pq pq0].
    by split => //; exact/set0P/eqP.
  case: Dnpi => [Dnp|pi].
  - case: Dnqi => [Dnq|qi].
    + case: (maxD n) => _ + _.
      move/trivIsetP => /(_ _ _ Dnp Dnq pq).
      by move/set0P : pq0 => /eqP.
    + have := Dn_Bi _ Dnp.
      by rewrite setIC -qi; move/set0P : pq0 => /eqP.
  - case: Dnqi => [Dnq|qi].
    + have := Dn_Bi _ Dnq.
      by rewrite -pi; move/set0P : pq0 => /eqP.
    + by move: pq; rewrite pi qi eqxx.
have Birn : (radius (B i))%:num <= r / (2 ^ n)%:R.
  by move: Bni; by rewrite /B_ /= => -[_] /andP[].
have Bjrn : (radius (B j))%:num > r / (2 ^ n.+1)%:R.
  have : \bigcup_(i < n.+1) D i `<=` \bigcup_(i < n.+1) (B_ i).
    move=> k [m/= mn] Dmk.
    have [+ _ _] := maxD m.
    by move/(_ _ Dmk) => -[Bmk] _; exists m.
  move/(_ _ Dj) => [m/= mn1] [_] /andP[+ _].
  apply: le_lt_trans.
  rewrite ler_pM2l ?(vitali_collection_partition_ub_gt0 Bset0 VBr Vi)//.
  by rewrite lef_pV2// ?posrE ?ltr0n ?expn_gt0// ler_nat leq_pexp2l.
exists j; split => //.
- by case: Dj => m /= mn Dm; exists m.
- rewrite (le_trans _ (ltW Bjrn))// ler_pdivrMr// expnSr natrM.
  by rewrite invrM ?unitfE// mulrAC -mulrA (mulrA 2) divff// div1r.
- move=> x Bix.
  rewrite is_ball_closure//; last first.
    by rewrite (ballE (is_ballB j)) scale_ballE; [exact: is_ball_ball|].
  rewrite closed_ballE; last first.
    rewrite (ballE (is_ballB j)) scale_ballE; last by [].
    by rewrite radius_ball_num ?mulr_ge0// mulr_gt0.
  rewrite /closed_ball_ /= cpoint_scale_ball; [|by []..].
  rewrite radius_scale_ball//.
  apply: (@le_trans _ _ (2 * (radius (B i))%:num + (radius (B j))%:num)).
    case: BiBj => y [Biy Bjy].
    rewrite (le_trans (ler_distD y _ _))// [in leRHS]addrC lerD//.
      exact: is_ball_closureP.
    rewrite (le_trans (ler_distD (cpoint (B i)) _ _))//.
    rewrite (_ : 2 = 1 + 1); last by [].
    rewrite mulrDl !mul1r// lerD; [by []| |exact: is_ball_closureP].
    by rewrite distrC; exact: is_ball_closureP.
  rewrite -lerBrDr// -(@natr1 _ 4).
  rewrite (mulrDl 4%:R) mul1r addrK (natrM _ 2 2) -mulrA ler_pM2l//.
  rewrite (le_trans Birn)// [in leRHS]mulrC -ler_pdivrMr//.
  by rewrite -mulrA -invfM -natrM -expnSr ltW.
Qed.

Lemma vitali_lemma_infinite_cover : { D : set I | [/\ countable D,
  D `<=` V, trivIset D (closure \o B) &
  cover V (closure \o B) `<=` cover D (closure \o scale_ball 5%:R \o B)] }.
Proof.
have [D [cD DV tD maxD]] := vitali_lemma_infinite.
exists D; split => // x [i Vi] cBix/=.
by have [j [Dj BiBj ij]] := maxD i Vi; move/(_ _ cBix) => ?; exists j.
Qed.

End vitali_lemma_infinite.

Section set_itv_realType.
Variable R : realType.
Implicit Types x : R.

Lemma set_itvK : {in neitv, cancel pred_set (@Rhull R)}.
Proof.
move=> [[[] x|[]] [[] y|[]]] /neitvP //;
  rewrite /Rhull /= !(in_itv, inE)/= ?bnd_simp => xy.
- rewrite asboolT// inf_itv// lexx/= xy asboolT// asboolT//=.
  by rewrite asboolF//= sup_itv//= ltxx ?andbF.
- by rewrite asboolT// inf_itv// ?asboolT// ?sup_itv// ?lexx ?xy.
- by rewrite asboolT//= inf_itv// lexx asboolT// asboolF.
- rewrite asboolT// inf_itv//= ltxx asboolF// asboolT//.
  by rewrite sup_itv// ltxx andbF asboolF.
  rewrite asboolT // inf_itv // ltxx asboolF // asboolT //.
  by rewrite sup_itv // xy lexx asboolT.
- by rewrite asboolT // inf_itv// ltxx asboolF // asboolF.
- by rewrite asboolF // asboolT // sup_itv// ltxx asboolF.
- by rewrite asboolF // asboolT // sup_itv// lexx asboolT.
- by rewrite asboolF // asboolF.
Qed.

Lemma RhullT : Rhull setT = `]-oo, +oo[%R :> interval R.
Proof. by rewrite /Rhull -set_itv_infty_infty asboolF// asboolF. Qed.

Lemma RhullK : {in (@is_interval _ : set (set R)), cancel (@Rhull R) pred_set}.
Proof. by move=> X /asboolP iX; apply/esym/is_intervalP. Qed.

Lemma set_itv_setT (i : interval R) : [set` i] = setT -> i = `]-oo, +oo[.
Proof.
have [i0  /(congr1 (@Rhull _))|] := boolP (neitv i).
  by rewrite set_itvK// => ->; exact: RhullT.
by rewrite negbK => /eqP ->; rewrite predeqE => /(_ 0)[_]/(_ Logic.I).
Qed.

End set_itv_realType.

Section Rhull_lemmas.
Variable R : realType.
Implicit Types (a b t r : R) (A : set R).

Lemma Rhull_smallest A : [set` Rhull A] = smallest (@is_interval R) A.
Proof.
apply/seteqP; split; last first.
  by apply: smallest_sub; [apply: interval_is_interval | apply: sub_Rhull].
move=> x /= + I [Iitv AI]; rewrite /Rhull.
have [|] := asboolP (has_lbound A) => lA; last first.
  have /forallNP/(_ x)/existsNP[a] := lA.
  move=> /existsNP[Aa /negP]; rewrite -ltNge => ax.
  have [|]:= asboolP (has_ubound A) => uA; last first.
    move=> ?; have /forallNP/(_ x)/existsNP[b] := uA.
    move=> /existsNP[Ab /negP]; rewrite -ltNge => xb.
    have /is_intervalPlt/(_ a b) := Iitv; apply; do ?by apply: AI.
    by rewrite ax xb.
  have [As|NAs]/= := asboolP (A _) => xA.
    by apply: (Iitv a (sup A)); by [apply: AI | rewrite ltW ?ax].
  have [||b Ab xb] := @sup_gt _ A x; do ?by [exists a | rewrite (itvP xA)].
  have /is_intervalPlt/(_ a b) := Iitv; apply; do ?by apply: AI.
  by rewrite ax xb.
have [|]:= asboolP (has_ubound A) => uA; last first.
  have /forallNP/(_ x)/existsNP[b] := uA.
  move=> /existsNP[Ab /negP]; rewrite -ltNge => xb.
  have [Ai|NAi]/= := asboolP (A _) => xA.
    by apply: (Iitv (inf A) b); by [apply: AI | rewrite (ltW xb)].
  have [||a Aa ax] := @inf_lt _ A x; do ?by [exists b | rewrite (itvP xA)].
  have /is_intervalPlt/(_ a b) := Iitv; apply; do ?by apply: AI.
  by rewrite ax xb.
have [Ai|NAi]/= := asboolP (A _); have [As|NAs]/= := asboolP (A _).
- by apply: Iitv; apply: AI.
- move=> xA.
  have [||b Ab xb] := @sup_gt _ A x; do ?by [exists (inf A) | rewrite (itvP xA)].
  have /(_ (inf A) b) := Iitv; apply; do ?by apply: AI.
  by rewrite (itvP xA) (ltW xb).
- move=> xA.
  have [||a Aa ax] := @inf_lt _ A x; do ?by [exists (sup A) | rewrite (itvP xA)].
  have /(_ a (sup A)) := Iitv; apply; do ?by apply: AI.
  by rewrite (itvP xA) (ltW ax).
have [->|/set0P AN0] := eqVneq A set0.
  by rewrite inf0 sup0 itv_ge//= ltBSide/= ltxx.
move=> xA.
have [||a Aa ax] := @inf_lt _ A x; do ?by [|rewrite (itvP xA)].
have [||b Ab xb] := @sup_gt _ A x; do ?by [|rewrite (itvP xA)].
have /is_intervalPlt/(_ a b) := Iitv; apply; do ?by apply: AI.
by rewrite ax xb.
Qed.

Lemma le_Rhull : {homo (@Rhull R) : A B / (A `<=` B) >-> {subset A <= B}}.
Proof.
move=> A B AB; suff: [set` Rhull A] `<=` [set` Rhull B] by [].
rewrite Rhull_smallest; apply: smallest_sub; first exact: interval_is_interval.
by rewrite Rhull_smallest; apply: sub_smallest.
Qed.

Lemma neitv_Rhull A : ~~ neitv (Rhull A) -> A = set0.
Proof.
move/negPn/eqP => A0; rewrite predeqE => r; split => // /sub_Rhull.
by rewrite A0.
Qed.

Lemma Rhull_involutive A : Rhull [set` Rhull A] = Rhull A.
Proof.
have [A0|/neitv_Rhull] := boolP (neitv (Rhull A)); first by rewrite set_itvK.
by move=> ->; rewrite ?Rhull0 set_itvE Rhull0.
Qed.

End Rhull_lemmas.

Lemma disj_itv_Rhull {R : realType} (A B : set R) : A `&` B = set0 ->
  is_interval A -> is_interval B -> disjoint_itv (Rhull A) (Rhull B).
Proof.
by move=> AB0 iA iB; rewrite /disjoint_itv RhullK ?inE// RhullK ?inE.
Qed.
