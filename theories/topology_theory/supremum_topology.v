(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra finmap all_classical.
From mathcomp Require Import topology_structure uniform_structure.

(**md**************************************************************************)
(* # Supremum topology                                                        *)
(*                                                                            *)
(* ```                                                                        *)
(*                  sup_topology Tc == supremum topology of the family of     *)
(*                                     topologicalType structures Tc on T     *)
(*                        sup_ent E == the entourages of the supremum         *)
(* ```                                                                        *)
(* `sup_topology` is equipped with the `Uniform` structure                         *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Definition sup_topology {T : Type} {I : Type}
  (Tc : I -> Topological T) : Type := T.

Section Sup_Topology.
Variable (T : choiceType) (I : Type) (Tc : I -> Topological T).
Local Notation S := (sup_topology Tc).

Let TS := fun i => Topological.Pack (Tc i).

Definition sup_subbase := \bigcup_i (@open (TS i) : set_system T).

HB.instance Definition _ := Choice.on S.
HB.instance Definition _ := isSubBaseTopological.Build S sup_subbase id.

Lemma cvg_sup (F : set_system T) (t : T) :
  Filter F -> F --> (t : S) <-> forall i, F --> (t : TS i).
Proof.
move=> Ffilt; split=> cvFt.
  move=> i A /=; rewrite (@nbhsE (TS i)) => - [B [Bop Bt] sBA].
  apply: cvFt; exists B; split=> //; exists [set B]; last first.
    by rewrite predeqE => ?; split=> [[_ ->]|] //; exists B.
  move=> _ ->; exists [fset B]%fset.
    by move=> ?; rewrite inE inE => /eqP->; exists i.
  by rewrite predeqE=> ?; split=> [|??]; [apply|]; rewrite /= inE // =>/eqP->.
move=> A /=; rewrite (@nbhsE [the topologicalType of S]).
move=> [_ [[B sB <-] [C BC Ct] sUBA]].
rewrite nbhs_filterE; apply: filterS sUBA _; apply: (@filterS _ _ _ C).
  by move=> ? ?; exists C.
have /sB [D sD IDeC] := BC; rewrite -IDeC; apply: filter_bigI => E DE.
have /sD := DE; rewrite inE => - [i _]; rewrite openE => Eop.
by apply: (cvFt i); apply: Eop; move: Ct; rewrite -IDeC => /(_ _ DE).
Qed.

End Sup_Topology.

HB.instance Definition _ (I : Type) (T : pointedType) (f : I -> Topological T) :=
  Pointed.on (sup_topology f).

Section sup_uniform.
Local Open Scope relation_scope.
Variable (T : choiceType) (Ii : Type) (Tc : Ii -> Uniform T).

Let I : choiceType := {classic Ii}.
Let TS := fun i => Uniform.Pack (Tc i).
Notation Tt := (sup_topology Tc).
Let ent_of (p : I * set (T * T)) := `[< @entourage (TS p.1) p.2 >].
Let IEntType := {p : (I * set (T * T)) | ent_of p}.
Let IEnt : choiceType := IEntType.

Local Lemma IEnt_pointT (i : I) : ent_of (i, setT).
Proof. by apply/asboolP; exact: entourageT. Qed.

Definition sup_ent : set_system (T * T) :=
  filter_from (finI_from [set: IEnt] (fun p => (projT1 p).2)) id.

Ltac IEntP := move=> [[ /= + + /[dup] /asboolP]].

Local Lemma sup_ent_filter : Filter sup_ent.
Proof.
case: (pselect (exists t:T, True)).
  case => p _; apply: finI_filter; move=> J JsubEnt /=; exists (p, p).
  by IEntP => i b /= /entourage_refl ? ? _.
move=> empT.
have TT0 (E : set (T*T)) : E = set0.
  rewrite eqEsubset; split => //=; case=> t ? _; move: empT.
  by apply: Logic.absurd; exists t.
have ent0 : sup_ent set0.
  rewrite -(TT0 setT); exists set0 => //=; exists fset0 => //=.
split.
- rewrite (TT0 setT); exact: ent0.
- by move => P Q ? ?; rewrite (TT0 (P `&` Q)).
- by move=> P Q _ _; rewrite (TT0 Q).
Qed.

Local Lemma sup_ent_refl A : sup_ent A -> diagonal `<=` A.
Proof.
move=> [B [F ? <-] BA] [? ?]/diagonalP ->; apply/BA.
by IEntP => i w /= /entourage_refl.
Qed.

Local Lemma sup_ent_inv A : sup_ent A -> sup_ent A^-1.
Proof.
move=> [B [F ? FB] BA]; exists B^-1; last by move=> ?; exact: BA.
have inv : forall ie : IEnt, ent_of ((projT1 ie).1, (projT1 ie).2^-1).
  by IEntP=> ?? /entourage_inv ??; exact/asboolP.
exists [fset (fun x => @exist (I * set (T * T)) _ _ (inv x)) w | w in F]%fset.
  by move=> ? /imfsetP; IEntP => ? ? ? ? ->; exact: in_setT.
rewrite -FB eqEsubset; split; case=> x y + ie.
  by move=> /(_ (exist ent_of _ (inv ie))) + ?; apply; apply/imfsetP; exists ie.
by move=> + /imfsetP [v vW ->]; exact.
Qed.

Local Lemma sup_ent_split A : sup_ent A -> exists2 B, sup_ent B & B \; B `<=` A.
Proof.
have spt : (forall ie : IEnt, ent_of ((projT1 ie).1,
    (@split_ent (TS (projT1 ie).1) (projT1 ie).2))).
  by case=> [[/= ? ?] /asboolP/entourage_split_ent ?]; exact/asboolP.
pose g : (IEnt -> IEnt) := fun x => exist ent_of _ (spt x).
case => W [F _ <-] sA; exists (\bigcap_(x in [set` F]) (projT1 (g x)).2).
  exists (\bigcap_(ie in [set`F]) (projT1 (g ie)).2) => //.
  exists [fset (g ie) | ie in F]%fset; first by move=> /= ??; exact: in_setT.
  rewrite eqEsubset; split; case=> x y Igxy ie.
    by move => ?; apply/(Igxy (g ie))/imfsetP; exists ie.
  by move=> /imfsetP [?? ->]; exact: Igxy.
case => ?? [z Fxz Fzy]; apply: sA; IEntP=> i e ? ? eF.
apply: ((@entourage_split (TS i)) z) => //.
  exact: (Fxz _ eF).
exact: (Fzy _ eF).
Qed.

Local Lemma sup_ent_nbhs : @nbhs Tt Tt = nbhs_ sup_ent.
Proof.
rewrite predeq2E => x V; split.
  move=> [/= X [[/= B + <-] [W BW Wx BV]]] => /(_ W BW) [] /=.
  move=> F Fsup Weq; move: Weq Wx BW => <- Fx BF.
  case (pselect ([set: I] = set0)) => [I0 | /eqP/set0P [i0 _]].
    suff -> : V = setT  by exists setT; apply: filterT; exact: sup_ent_filter.
    rewrite -subTset => ??; apply: BV; exists (\bigcap_(i in [set` F]) i) => //.
    by move=> w /Fsup/set_mem; rewrite /sup_subbase I0 bigcup_set0.
  have f : forall w, {p : IEnt |  w \in F -> xsection ((projT1 p).2) x `<=` w}.
    move=> /= v; apply: cid; case (pselect (v \in F)); first last.
      by move=> ?; exists (exist ent_of _ (IEnt_pointT i0)).
    move=> /[dup] /Fx vx /Fsup/set_mem [i _]; rewrite openE => /(_ x vx).
    by move=> /(@nbhsP (TS i)) [w /asboolP ent ?]; exists (exist _ (i, w) ent).
  exists (\bigcap_(w in [set` F]) (projT1 (projT1 (f w))).2); first last.
    move=> v /= /xsectionP Fgw; apply: BV; exists (\bigcap_(i in [set` F]) i) => //.
    by move=> w /[dup] ? /Fgw /= /mem_set/(projT2 (f w)); exact.
  exists (\bigcap_(w in [set` F]) (projT1 (projT1 (f w))).2) => //.
  exists [fset (fun i => projT1 (f i)) w | w in F]%fset.
    by move=> u ?; exact: in_setT.
  rewrite eqEsubset; split => y + z.
    by move=>/(_ (projT1 (f z))) => + ?; apply; apply/imfsetP; exists z.
  by move=> Fgy /imfsetP [/= u uF ->]; exact: Fgy.
case=> E [D [/= F FsubEnt <-] FsubE EsubV].
have F_nbhs_x : Filter (nbhs x) by typeclasses eauto.
apply: (filterS EsubV).
pose f : IEnt -> set T := fun w =>
  @interior (TS (projT1 w).1) (xsection (projT1 w).2 x).
exists (\bigcap_(w in [set` F]) f w); repeat split.
- exists [set \bigcap_(w in [set` F]) f w]; last by rewrite bigcup_set1.
  move=> ? ->; exists [fset f w | w in F]%fset.
    move=> /= ? /imfsetP [[[/= i w /[dup] /asboolP entw ? Fiw ->]]].
    by apply/mem_set; rewrite /f /=; exists i => //; exact: open_interior.
  by rewrite set_imfset bigcap_image //=.
- by IEntP=> ? ? /open_nbhs_entourage entw ??; apply entw.
- move=> t /= Ifwt.
  by apply/mem_set/FsubE => it /Ifwt/interior_subset => /set_mem.
Qed.

HB.instance Definition _ := @Nbhs_isUniform.Build Tt sup_ent
   sup_ent_filter sup_ent_refl sup_ent_inv sup_ent_split sup_ent_nbhs.

Lemma countable_sup_ent :
  countable [set: Ii] -> (forall n, countable_uniformity (TS n)) ->
  countable_uniformity Tt.
Proof.
move=> Icnt countable_ent; pose f n := cid (countable_ent n).
pose g (n : Ii) : set (set (T * T)) := projT1 (f n).
have [I0 | /set0P [i0 _]] := eqVneq [set: I] set0.
  exists [set setT]; split; [exact: countable1|move=> A ->; exact: entourageT|].
  move=> P [w [A _]] <- subP; exists setT => //.
  apply: subset_trans subP; apply: sub_bigcap => i _ ? _.
  by suff : [set: I] (projT1 i).1 by rewrite I0.
exists (finI_from (\bigcup_n g n) id); split.
- by apply/finI_from_countable/bigcup_countable => //i _; case: (projT2 (f i)).
- move=> E [A AsubGn AE]; exists E => //.
  have h (w : set (T * T)) : { p : IEnt | w \in A -> w = (projT1 p).2 }.
    apply: cid; have [|] := boolP (w \in A); last first.
      by exists (exist ent_of _ (IEnt_pointT i0)).
    move=> /[dup] /AsubGn /set_mem [n _ gnw] wA.
    suff ent : ent_of (n, w) by exists (exist ent_of (n, w) ent).
    by apply/asboolP; have [_ + _] := projT2 (f n); exact.
  exists [fset sval (h w) | w in A]%fset; first by move=> ?; exact: in_setT.
  rewrite -AE; rewrite eqEsubset; split => t Ia.
    by move=> w Aw; rewrite (svalP (h w) Aw); apply/Ia/imfsetP; exists w.
  case=> [[n w]] p /imfsetP [x /= xA M]; apply: Ia.
  by rewrite (_ : w = x) // (svalP (h x) xA) -M.
- move=> E [w] [ A _ wIA wsubE].
  have ent_Ip (i : IEnt) : @entourage (TS (projT1 i).1) (projT1 i).2.
    by apply/asboolP; exact: (projT2 i).
  pose h (i : IEnt) : {x : set (T * T) | _} := cid2 (and3_rec
    (fun _ _ P => P) (projT2 (f (projT1 i).1)) (projT1 i).2 (ent_Ip i)).
  have ehi (i : IEnt) : ent_of ((projT1 i).1, projT1 (h i)).
    apply/asboolP => /=; have [] := projT2 (h i).
    by have [_ + _ ? ?] := projT2 (f (projT1 i).1); exact.
  pose AH := [fset projT1 (h w) | w in A]%fset.
  exists (\bigcap_(i in [set` AH]) i).
    exists AH => // p /imfsetP [i iA ->]; rewrite inE //.
    by exists (projT1 i).1 => //; have [] := projT2 (h i).
  apply: subset_trans wsubE; rewrite -wIA => ? It i ?.
  by have [?] := projT2 (h i); apply; apply: It; apply/imfsetP; exists i.
Qed.

End sup_uniform.
