(* mathcomp analysis (c) 2026 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
#[warning="-warn-library-file-internal-analysis"]
From mathcomp Require Import unstable.
From mathcomp Require Import boolp classical_sets functions cardinality reals.
From mathcomp Require Import ereal topology normedtype.
From mathcomp Require Import sequences measurable_structure.

(**md**************************************************************************)
(* # Measurable Functions                                                     *)
(*                                                                            *)
(* ```                                                                        *)
(*        measurable_fun D f == the function f with domain D is measurable    *)
(*          {mfun aT >-> rT} == type of measurable functions                  *)
(*                              aT and rT are sigmaRingType's.                *)
(*                f \in mfun == holds for f : {mfun _ >-> _}                  *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "{ 'mfun' aT >-> T }"
  (at level 0, format "{ 'mfun'  aT  >->  T }").
Reserved Notation "[ 'mfun' 'of' f ]"
  (at level 0, format "[ 'mfun'  'of'  f ]").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import ProperNotations.
Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Definition measurable_fun d d' (T : sigmaRingType d) (U : sigmaRingType d')
    (D : set T) (f : T -> U) :=
  measurable D -> forall Y, measurable Y -> measurable (D `&` f @^-1` Y).

HB.mixin Record isMeasurableFun d d' (aT : sigmaRingType d) (rT : sigmaRingType d')
    (f : aT -> rT) := {
  measurable_funPT : measurable_fun [set: aT] f
}.

HB.structure Definition MeasurableFun d d' aT rT :=
  {f of @isMeasurableFun d d' aT rT f}.
Arguments measurable_funPT {d d' aT rT} s.

Notation "{ 'mfun' aT >-> T }" := (@MeasurableFun.type _ _ aT T) : form_scope.
Notation "[ 'mfun' 'of' f ]" := [the {mfun _ >-> _} of f] : form_scope.
#[global] Hint Extern 0 (measurable_fun [set: _] _) =>
  solve [apply: measurable_funPT] : core.

Lemma measurable_funP {d d' : measure_display}
  {aT : measurableType d} {rT : sigmaRingType d'}
  (D : set aT) (s : {mfun aT >-> rT}) : measurable_fun D s.
Proof.
move=> mD Y mY; apply: measurableI => //.
by rewrite -(setTI (_ @^-1` _)); exact: measurable_funPT.
Qed.
Arguments measurable_funP {d d' aT rT D} s.

Lemma measurable_funPTI {d d'} {aT : measurableType d} {rT : measurableType d'}
  (f : {mfun aT >-> rT}) (Y : set rT) : measurable Y -> measurable (f @^-1` Y).
Proof. by move=> mY; rewrite -[f @^-1` _]setTI; exact: measurable_funP. Qed.

#[deprecated(since="mathcomp-analysis 1.13.0", note="renamed to `measurable_funPTI`")]
Notation measurable_sfunP := measurable_funPTI (only parsing).

Section mfun_pred.
Context {d d'} {aT : sigmaRingType d} {rT : sigmaRingType d'}.
Definition mfun : {pred aT -> rT} := mem [set f | measurable_fun setT f].
Definition mfun_key : pred_key mfun. Proof. exact. Qed.
Canonical mfun_keyed := KeyedPred mfun_key.
End mfun_pred.

Section measurable_fun.
Context d1 d2 d3 (T1 : sigmaRingType d1) (T2 : sigmaRingType d2)
        (T3 : sigmaRingType d3).
Implicit Type D E : set T1.

Lemma measurable_id D : measurable_fun D id.
Proof. by move=> mD A mA; apply: measurableI. Qed.

Lemma measurable_comp F (f : T2 -> T3) E (g : T1 -> T2) :
  measurable F -> g @` E `<=` F ->
  measurable_fun F f -> measurable_fun E g -> measurable_fun E (f \o g).
Proof.
move=> mF FgE mf mg /= mE A mA.
rewrite comp_preimage.
rewrite (_ : _ `&` _ = E `&` g @^-1` (F `&` f @^-1` A)); last first.
  apply/seteqP; split=> [|? [?] []//].
  by move=> x/= [Ex Afgx]; split => //; split => //; exact: FgE.
by apply/mg => //; exact: mf.
Qed.

Lemma eq_measurable_fun D (f g : T1 -> T2) :
  {in D, f =1 g} -> measurable_fun D f -> measurable_fun D g.
Proof.
by move=> fg mf mD A mA; rewrite [X in measurable X](_ : _ = D `&` f @^-1` A);
  [exact: mf|exact/esym/eq_preimage].
Qed.

Lemma measurable_fun_eqP D (f g : T1 -> T2) :
  {in D, f =1 g} -> measurable_fun D f <-> measurable_fun D g.
Proof.
by move=> eq_fg; split; apply/eq_measurable_fun => // ? ?; rewrite eq_fg.
Qed.

Lemma measurable_cst D (r : T2) : measurable_fun D (cst r : T1 -> _).
Proof.
by move=> mD /= Y mY; rewrite preimage_cst; case: ifPn; rewrite ?setIT ?setI0.
Qed.

Lemma measurable_fun_bigcup (E : (set T1)^nat) (f : T1 -> T2) :
  (forall i, measurable (E i)) ->
  measurable_fun (\bigcup_i E i) f <-> (forall i, measurable_fun (E i) f).
Proof.
move=> mE; split => [|mf /= _ A mA]; last first.
  by rewrite setI_bigcupl; apply: bigcup_measurable => i _; exact: mf.
move=> mf i _ A /mf => /(_ (bigcup_measurable (fun k _ => mE k))).
move=> /(measurableI (E i))-/(_ (mE i)).
by rewrite setICA setIA (@setIidr _ _ (E i))//; exact: bigcup_sup.
Qed.

Lemma measurable_funU D E (f : T1 -> T2) : measurable D -> measurable E ->
  measurable_fun (D `|` E) f <-> measurable_fun D f /\ measurable_fun E f.
Proof.
move=> mD mE; rewrite -bigcup2E; apply: (iff_trans (measurable_fun_bigcup _ _)).
  by move=> [//|[//|//=]].
split=> [mf|[Df Dg] [//|[//|/= _ _ Y mY]]]; last by rewrite set0I.
by split; [exact: (mf 0%N)|exact: (mf 1%N)].
Qed.

Lemma measurable_funS E D (f : T1 -> T2) :
    measurable E -> D `<=` E -> measurable_fun E f ->
  measurable_fun D f.
Proof.
move=> mE DE mf mD; have mC : measurable (E `\` D) by exact: measurableD.
move: (mD).
have := measurable_funU f mD mC.
suff -> : D `|` (E `\` D) = E by move=> [[]] //.
by rewrite setDUK.
Qed.

Lemma measurable_fun_if (g h : T1 -> T2) D (mD : measurable D)
    (f : T1 -> bool) (mf : measurable_fun D f) :
  measurable_fun (D `&` (f @^-1` [set true])) g ->
  measurable_fun (D `&` (f @^-1` [set false])) h ->
  measurable_fun D (fun t => if f t then g t else h t).
Proof.
move=> mx my /= _ B mB; rewrite (_ : _ @^-1` B =
    ((f @^-1` [set true]) `&` (g @^-1` B)) `|`
    ((f @^-1` [set false]) `&` (h @^-1` B))).
  rewrite setIUr; apply: measurableU.
  - by rewrite setIA; apply: mx => //; exact: mf.
  - by rewrite setIA; apply: my => //; exact: mf.
apply/seteqP; split=> [t /=| t /= [] [] ->//].
by case: ifPn => ft; [left|right].
Qed.

Lemma measurable_fun_set0 (f : T1 -> T2) : measurable_fun set0 f.
Proof. by move=> A B _; rewrite set0I. Qed.

Lemma measurable_fun_set1 a (f : T1 -> T2) : measurable_fun [set a] f.
Proof. by move=> ? ? ?; rewrite set1I; case: ifP. Qed.

End measurable_fun.
#[global] Hint Extern 0 (measurable_fun _ (fun=> _)) =>
  solve [apply: measurable_cst] : core.
#[global] Hint Extern 0 (measurable_fun _ (cst _)) =>
  solve [apply: measurable_cst] : core.
#[global] Hint Extern 0 (measurable_fun _ id) =>
  solve [apply: measurable_id] : core.
Arguments eq_measurable_fun {d1 d2 T1 T2 D} f {g}.
Arguments measurable_fun_eqP {d1 d2 T1 T2 D} f {g}.

Section mfun.
Context {d d'} {aT : sigmaRingType d} {rT : sigmaRingType d'}.
Notation T := {mfun aT >-> rT}.
Notation mfun := (@mfun _ _ aT rT).

Section Sub.
Context (f : aT -> rT) (fP : f \in mfun).
Definition mfun_Sub_subproof := @isMeasurableFun.Build d _ aT rT f (set_mem fP).
#[local] HB.instance Definition _ := mfun_Sub_subproof.
Definition mfun_Sub := [mfun of f].
End Sub.

Lemma mfun_rect (K : T -> Type) :
  (forall f (Pf : f \in mfun), K (mfun_Sub Pf)) -> forall u : T, K u.
Proof.
move=> Ksub [f [[Pf]]]/=.
by suff -> : Pf = (set_mem (@mem_set _ [set f | _] f Pf)) by apply: Ksub.
Qed.

Lemma mfun_valP f (Pf : f \in mfun) : mfun_Sub Pf = f :> (_ -> _).
Proof. by []. Qed.

HB.instance Definition _ := isSub.Build _ _ T mfun_rect mfun_valP.

Lemma mfuneqP (f g : {mfun aT >-> rT}) : f = g <-> f =1 g.
Proof. by split=> [->//|fg]; apply/val_inj/funext. Qed.

HB.instance Definition _ := [Choice of {mfun aT >-> rT} by <:].

HB.instance Definition _ x := isMeasurableFun.Build d _ aT rT (cst x)
  (@measurable_cst _ _ aT rT setT x).

End mfun.

Section measurable_fun_measurableType.
Context d1 d2 d3 (T1 : measurableType d1) (T2 : measurableType d2)
        (T3 : measurableType d3).
Implicit Type D E : set T1.

Lemma measurableT_comp (f : T2 -> T3) E (g : T1 -> T2) :
  measurable_fun [set: T2] f -> measurable_fun E g -> measurable_fun E (f \o g).
Proof. exact: measurable_comp. Qed.

Lemma measurable_funTS D (f : T1 -> T2) :
  measurable_fun [set: T1] f -> measurable_fun D f.
Proof. exact: measurable_funS. Qed.

Lemma measurable_restrict D E (f : T1 -> T2) : measurable D -> measurable E ->
  measurable_fun (E `&` D) f <-> measurable_fun E (f \_ D).
Proof.
move=> mD mE; split => mf _ /= Y mY.
- rewrite preimage_restrict; case: ifPn => ptX; last first.
    by rewrite set0U setIA; apply: mf => //; exact: measurableI.
  rewrite setIUr; apply: measurableU.
    by apply: measurableI => //; exact: measurableC.
  by rewrite setIA; apply: mf => //; exact: measurableI.
- have := mf mE _ mY; rewrite preimage_restrict; case: ifP => ptY; last first.
    by rewrite set0U setIA.
  rewrite setUIr setvU setTI setIUr => /(measurableI _ _ mD).
  by rewrite setIUr setIA setIAC setICr set0I set0U setICA setIA.
Qed.

Lemma measurable_restrictT D (f : T1 -> T2) : measurable D ->
  measurable_fun D f <-> measurable_fun [set: T1] (f \_ D).
Proof.
by move=> mD; have := measurable_restrict f mD measurableT; rewrite setTI.
Qed.

Lemma measurable_fun_ifT (g h : T1 -> T2) (f : T1 -> bool)
    (mf : measurable_fun [set: T1] f) :
  measurable_fun [set: T1] g -> measurable_fun [set: T1] h ->
  measurable_fun [set: T1] (fun t => if f t then g t else h t).
Proof.
by move=> mx my; apply: measurable_fun_if => //;
  [exact: measurable_funS mx|exact: measurable_funS my].
Qed.

Section measurable_fun_bool.
Implicit Types f g : T1 -> bool.

Let measurable_fun_TF D f :
  measurable (D `&` f @^-1` [set true]) ->
  measurable (D `&` f @^-1` [set false]) ->
  measurable_fun D f.
Proof.
move=> mT mF mD /= Y mY.
have := @subsetT _ Y; rewrite setT_bool => YT.
move: mY; have [-> _|-> _|-> _ |-> _] := subset_set2 YT.
- by rewrite preimage0 ?setI0.
- exact: mT.
- exact: mF.
- by rewrite -setT_bool preimage_setT setIT.
Qed.

Lemma measurable_fun_bool D f b :
  measurable (D `&` f @^-1` [set b]) -> measurable_fun D f.
Proof.
move=> mb mD; have mDb : measurable (D `&` f @^-1` [set ~~ b]).
  rewrite (_ : [set ~~ b] = [set~ b]); last first.
    by apply/seteqP; split=> -[] /=; case: b {mb}.
  by rewrite -preimage_setC; exact: measurableID.
by case: b => /= in mb mDb *; exact: measurable_fun_TF.
Qed.
#[global] Arguments measurable_fun_bool {D f} _.

Lemma measurable_and D f g : measurable_fun D f -> measurable_fun D g ->
  measurable_fun D (fun x => f x && g x).
Proof.
move=> mf mg mD; apply: (measurable_fun_bool true) => //.
rewrite [X in measurable X](_ : _ = D `&` f @^-1` [set true] `&`
                                    (D `&` g @^-1` [set true])); last first.
  by rewrite setIACA setIid; congr (_ `&` _); apply/seteqP; split => x /andP.
by apply: measurableI; [exact: mf|exact: mg].
Qed.

Lemma measurable_neg D f :
  measurable_fun D f -> measurable_fun D (fun x => ~~ f x).
Proof.
move=> mf mD; apply: (measurable_fun_bool true) => //.
rewrite [X in measurable X](_ : _ = (D `&` f @^-1` [set false])).
  exact: mf.
by apply/seteqP; split => [x [Dx/= /negbTE]|x [Dx/= ->]].
Qed.

Lemma measurable_or D f g : measurable_fun D f -> measurable_fun D g ->
  measurable_fun D (fun x => f x || g x).
Proof.
move=> mf mg.
rewrite [X in measurable_fun _ X](_ : _ = (fun x => ~~ (~~ f x && ~~ g x))).
  by apply: measurable_neg; apply: measurable_and; exact: measurable_neg.
by apply/funext=> x; rewrite -negb_or negbK.
Qed.

End measurable_fun_bool.

End measurable_fun_measurableType.
#[global] Hint Extern 0 (measurable_fun _ (fun=> _)) =>
  solve [apply: measurable_cst] : core.
#[global] Hint Extern 0 (measurable_fun _ (cst _)) =>
  solve [apply: measurable_cst] : core.
#[global] Hint Extern 0 (measurable_fun _ id) =>
  solve [apply: measurable_id] : core.
Arguments eq_measurable_fun {d1 d2 T1 T2 D} f {g}.
Arguments measurable_fun_bool {d1 T1 D f} b.

Section mfun_measurableType.
Context {d1} {T1 : measurableType d1} {d2} {T2 : measurableType d2}
  {d3} {T3 : measurableType d3}.
Variables (f : {mfun T2 >-> T3}) (g : {mfun T1 >-> T2}).

Let measurableT_comp_subproof : measurable_fun setT (f \o g).
Proof. exact: measurableT_comp. Qed.

HB.instance Definition _ := isMeasurableFun.Build _ _ _ _ (f \o g)
  measurableT_comp_subproof.

End mfun_measurableType.

Section measurability.

(* f is measurable on the sigma-algebra generated by itself *)
Lemma preimage_set_system_measurable_fun d (aT : pointedType)
    (rT : measurableType d) (D : set aT) (f : aT -> rT) :
  measurable_fun
    (D : set (g_sigma_algebraType (preimage_set_system D f measurable))) f.
Proof. by move=> mD A mA; apply: sub_sigma_algebra; exists A. Qed.

Lemma measurability d d' (aT : measurableType d) (rT : measurableType d')
    (D : set aT) (f : aT -> rT) (G : set (set rT)) :
  @measurable _ rT = <<s G >> -> preimage_set_system D f G `<=` @measurable _ aT ->
  measurable_fun D f.
Proof.
move=> sG_rT fG_aT mD.
suff h : preimage_set_system D f (@measurable _ rT) `<=` @measurable _ aT.
  by move=> A mA; apply: h; exists A.
have -> : preimage_set_system D f (@measurable _ rT) =
         <<s D, preimage_set_system D f G >>.
  by rewrite [in LHS]sG_rT [in RHS]g_sigma_preimageE.
apply: smallest_sub => //; split => //.
- by move=> A mA; exact: measurableD.
- by move=> F h; exact: bigcupT_measurable.
Qed.

End measurability.
#[deprecated(since="mathcomp-analysis 1.9.0", note="renamed to `preimage_set_system_measurable_fun`")]
Notation preimage_class_measurable_fun := preimage_set_system_measurable_fun (only parsing).
Arguments measurability {d d' aT rT D f} _.

Section prod_measurable_fun.
Context d d1 d2 (T : measurableType d) (T1 : measurableType d1)
        (T2 : measurableType d2).

Lemma measurable_fun_pairP (h : T -> T1 * T2) : measurable_fun setT h <->
  measurable_fun setT (fst \o h) /\ measurable_fun setT (snd \o h).
Proof.
apply: (@iff_trans _ (g_sigma_preimageU (fst \o h) (snd \o h) `<=` measurable)).
- rewrite g_sigma_preimageU_comp; split=> [mf A [C HC <-]|f12]; first exact: mf.
  by move=> _ A mA; apply: f12; exists A.
- split => [h12|[mf1 mf2]].
    split => _ A mA; apply: h12; apply: sub_sigma_algebra;
    by [left; exists A|right; exists A].
  apply: smallest_sub; first exact: sigma_algebra_measurable.
  by rewrite subUset; split=> [|] A [C mC <-]; [exact: mf1|exact: mf2].
Qed.

Lemma measurable_fun_pair (f : T -> T1) (g : T -> T2) :
  measurable_fun setT f -> measurable_fun setT g ->
  measurable_fun setT (fun x => (f x, g x)).
Proof. by move=> mf mg; exact/measurable_fun_pairP. Qed.

End prod_measurable_fun.
#[deprecated(since="mathcomp-analysis 1.10.0", note="renamed `measurable_fun_pair`")]
Notation measurable_fun_prod := measurable_fun_pair (only parsing).
#[deprecated(since="mathcomp-analysis 1.10.0", note="renamed `measurable_fun_pairP`")]
Notation prod_measurable_funP := measurable_fun_pairP (only parsing).

Section prod_measurable_proj.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2).

Lemma measurable_fst : measurable_fun [set: T1 * T2] fst.
Proof.
by have /measurable_fun_pairP[] := @measurable_id _ (T1 * T2)%type setT.
Qed.
#[local] Hint Resolve measurable_fst : core.

Lemma measurable_snd : measurable_fun [set: T1 * T2] snd.
Proof.
by have /measurable_fun_pairP[] := @measurable_id _ (T1 * T2)%type setT.
Qed.
#[local] Hint Resolve measurable_snd : core.

Lemma measurable_swap : measurable_fun [set: _] (@swap T1 T2).
Proof. exact: measurable_fun_pair. Qed.

End prod_measurable_proj.
Arguments measurable_fst {d1 d2 T1 T2}.
Arguments measurable_snd {d1 d2 T1 T2}.
#[global] Hint Extern 0 (measurable_fun _ fst) =>
  solve [apply: measurable_fst] : core.
#[global] Hint Extern 0 (measurable_fun _ snd) =>
  solve [apply: measurable_snd] : core.

Lemma measurable_tnth d (T : sigmaRingType d) n (i : 'I_n) :
  measurable_fun [set: n.-tuple T] (@tnth _ T ^~ i).
Proof.
move=> _ Y mY; rewrite setTI; apply: sub_sigma_algebra => /=.
rewrite -bigcup_seq/=; exists i => /=; first by rewrite mem_index_enum.
by exists Y => //; rewrite setTI.
Qed.

Section measurable_cons.
Context d1 d2 (T1 : measurableType d1) (T2 : measurableType d2).

Lemma measurable_fun_tnthP n (f : T1 -> n.-tuple T2) :
  measurable_fun [set: T1] f <->
  forall i, measurable_fun [set: T1] (@tnth n T2 ^~ i \o f).
Proof.
apply: (@iff_trans _ (g_sigma_preimage
    (fun i => @tnth n T2 ^~ i \o f) `<=` measurable)).
  rewrite g_sigma_preimage_comp; split=> [mf A [/= C preC <-]|prefS].
    exact: mf.
  by move=> _ A mA; apply: prefS; exists A.
split=> [tnthfS i|mf].
- move=> _ A mA.
  apply: tnthfS; apply: sub_sigma_algebra.
  case: n i => [[] []//|n i] in f *.
  rewrite -bigcup_mkord_ord.
  exists i; first exact: ltn_ord.
  by exists A => //; rewrite inord_val.
- apply: smallest_sub; first exact: sigma_algebra_measurable.
  case: n => [|n] in f mf *; first by rewrite big_ord0.
  rewrite -bigcup_mkord_ord; apply: bigcup_sub => i Ii.
  by move=> A [B mB <-]; exact: mf.
Qed.

Lemma measurable_cons (f : T1 -> T2) n (g : T1 -> n.-tuple T2) :
  measurable_fun [set: T1] f -> measurable_fun [set: T1] g ->
  measurable_fun [set: T1] (fun x => [the n.+1.-tuple T2 of f x :: g x]).
Proof.
move=> mf mg; apply/measurable_fun_tnthP => /= i.
have [->//|i0] := eqVneq i ord0.
have i1n : (i.-1 < n)%N by rewrite prednK ?lt0n// -ltnS.
pose j := Ordinal i1n.
rewrite (_ : _ \o _ = fun x => tnth (g x) j)//.
  apply: (@measurableT_comp _ _ _ _ _ _ (fun x => tnth x j)) => //=.
  exact: measurable_tnth.
apply/funext => x /=.
rewrite (_ : i = lift ord0 j) ?tnthS//.
by apply/val_inj => /=; rewrite /bump/= add1n prednK// lt0n.
Qed.

End measurable_cons.

Lemma measurable_behead d (T : measurableType d) n :
  measurable_fun [set: n.+1.-tuple T] (fun x => [tuple of behead x]).
Proof.
move=> _ Y mY; rewrite setTI.
set f := fun x : (n.+1).-tuple T => [tuple of behead x] : n.-tuple T.
move: mY; rewrite /measurable/= => + F [] sF.
pose F' := image_set_system setT f F.
move=> /(_ F') /=.
have -> : F' Y = F (f @^-1` Y) by rewrite /F' /image_set_system /= setTI.
move=> /[swap] bigF; apply; split; first exact: sigma_algebra_image.
move=> A; rewrite /= {}/F' /image_set_system /= setTI.
set bign := (X in X A -> _) => bignA.
apply: bigF; rewrite big_ord_recl /=; right.
set bign1 := (X in X (_ @^-1` _)).
have -> : bign1 = preimage_set_system [set: n.+1.-tuple T] f bign.
  rewrite (big_morph _ (preimage_set_systemU _ _) (preimage_set_system0 _ _)).
  apply: eq_bigr => i _; rewrite -preimage_set_system_comp.
  congr preimage_set_system.
  by apply: funext=> t/=; rewrite [in LHS](tuple_eta t) tnthS.
by exists A => //; rewrite setTI.
Qed.

Lemma measurable_fun_if_pair d d' (X : measurableType d)
    (Y : measurableType d') (x y : X -> Y) :
  measurable_fun setT x -> measurable_fun setT y ->
  measurable_fun setT (fun tb => if tb.2 then x tb.1 else y tb.1).
Proof.
by move=> mx my; apply: measurable_fun_ifT => //=; exact: measurableT_comp.
Qed.

Section pair_measurable_fun.
Context d d1 d2 (T : measurableType d) (T1 : measurableType d1)
  (T2 : measurableType d2).
Variable f : T1 * T2 -> T.

Lemma pair1_measurable (x : T1) : measurable_fun [set: T2] (pair x).
Proof.
have m1pairx : measurable_fun [set: T2] (fst \o pair x) by exact/measurable_cst.
have m2pairx : measurable_fun [set: T2] (snd \o pair x) by exact/measurable_id.
exact/measurable_fun_pairP.
Qed.

Lemma pair2_measurable (y : T2) : measurable_fun [set: T1] (pair^~ y).
Proof.
have m1pairy : measurable_fun [set: T1] (fst \o pair^~y) by exact/measurable_id.
have m2pairy : measurable_fun [set: T1] (snd \o pair^~y) by exact/measurable_cst.
exact/measurable_fun_pairP.
Qed.

End pair_measurable_fun.
#[global] Hint Extern 0 (measurable_fun _ (pair _)) =>
  solve [apply: pair1_measurable] : core.
#[global] Hint Extern 0 (measurable_fun _ (pair^~ _)) =>
  solve [apply: pair2_measurable] : core.
#[deprecated(since="mathcomp-analysis 1.10.0", note="renamed `pair1_measurable`")]
Notation measurable_pair1 := pair1_measurable (only parsing).
#[deprecated(since="mathcomp-analysis 1.10.0", note="renamed `pair2_measurable`")]
Notation measurable_pair2 := pair2_measurable (only parsing).

(* [Lemma 14.13, Klenke 2014] *)
Section measurable_section.
Context d1 d2 d3 (T1 : measurableType d1) (T2 : measurableType d2)
  (T3 : measurableType d3).

Lemma measurable_xsection (A : set (T1 * T2)) (x : T1) :
  measurable A -> measurable (xsection A x).
Proof.
move=> mA; pose i (y : T2) := (x, y).
have mi : measurable_fun setT i by exact: pair1_measurable.
by rewrite xsectionE -[X in measurable X]setTI; exact: mi.
Qed.

Lemma measurable_ysection (A : set (T1 * T2)) (y : T2) :
  measurable A -> measurable (ysection A y).
Proof.
move=> mA; pose i (x : T1) := (x, y).
have mi : measurable_fun setT i by exact: pair2_measurable.
by rewrite ysectionE -[X in measurable X]setTI; exact: mi.
Qed.

Lemma measurable_fun_pair1 (f : T1 * T2 -> T3) (y : T2) :
  measurable_fun setT f -> measurable_fun setT (fun x => f (x, y)).
Proof. by move=> mf; exact: measurableT_comp. Qed.

Lemma measurable_fun_pair2 (f : T1 * T2 -> T3) (x : T1) :
  measurable_fun setT f -> measurable_fun setT (fun y => f (x, y)).
Proof. by move=> mf; exact: measurableT_comp. Qed.

End measurable_section.
