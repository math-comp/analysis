(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import boolp contra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section LocalProperties.

Context {T1 T2 T3 : Type} {T : predArgType}.
Implicit Type A : {pred T}.

Local Notation "{ 'allA' P }" := (forall A : {pred T}, P A : Prop) (at level 0).
Local Notation ph := (phantom _).

Definition prop_within d P & ph {allA P} := forall A, sub_mem (mem A) d -> P A.

Lemma withinW A P : {allA P} -> prop_within (mem A) (inPhantom {allA P}).
Proof. by move=> allP ? _; apply: allP. Qed.

Lemma withinT P : prop_within (mem T) (inPhantom {allA P}) -> {allA P}.
Proof. by move=> allP A; apply: allP. Qed.

Lemma sub_within d d' P :
  sub_mem d d' -> forall phP, @prop_within d' P phP -> @prop_within d P phP.
Proof. by move=> sdd' phP Pd' A /(_ _ _)/sdd'-/Pd'. Qed.

End LocalProperties.

Notation "{ 'in' <= S , P }" :=
  (prop_within (mem S) (inPhantom P)) : type_scope.

Section RelDefs.

Variables (T : Type) (R : rel T).
Implicit Types (x y z : T) (A C : {pred T}).

(* TOTHINK: This should be ported to mathcomp. *)
Definition maximal z := forall x, R z x -> R x z.

Definition minimal z := forall x, R x z -> R z x.

Definition upper_bound A z := {in A, forall x, R x z}.

Definition lower_bound A z := {in A, forall x, R z x}.

Definition preorder := reflexive R /\ transitive R.

Definition partial_order := preorder /\ antisymmetric R.

Definition total_order := partial_order /\ total R.

Definition nonempty A := exists x, x \in A.

Definition minimum_of A z := z \in A /\ lower_bound A z.

Definition maximum_of A z := z \in A /\ upper_bound A z.

Definition well_order := forall A, nonempty A -> exists! z, minimum_of A z.

Definition chain C := {in C &, total R}.

Definition wo_chain C := {in <= C, well_order}.

Lemma antisymmetric_wo_chain C :
    {in C &, antisymmetric R} ->
    {in <= C, forall A, nonempty A -> exists z, minimum_of A z} ->
  wo_chain C.
Proof.
move=> Ranti Rwo A sAC /Rwo[//|z [Az lbAz]]; exists z; split=> // x [Ax lbAx].
by apply: Ranti; rewrite ?sAC ?lbAx ?lbAz.
Qed.

Lemma antisymmetric_well_order :
    antisymmetric R -> (forall A, nonempty A -> exists z, minimum_of A z) ->
  well_order.
Proof.
by move=> Ranti /withinW/(antisymmetric_wo_chain (in2W Ranti))/withinT.
Qed.

End RelDefs.

Lemma wo_chainW (T : eqType) R C : @wo_chain T R C -> chain R C.
Proof.
have ne_cons x s: nonempty [mem x :: s : seq T] by exists x; apply: mem_head.
have all_mem s: all [mem s : seq T] s by apply/allP.
move=> Rwo x y Cx Cy; have /Rwo[] := ne_cons x [::y]; first exact/allP/and3P.
by move=> z [] [] /or3P[] // /eqP-> /allP/and3P[] => [_|] ->; rewrite ?orbT.
Qed.

Lemma wo_chain_reflexive (T : eqType) R C : @wo_chain T R C -> {in C, reflexive R}.
Proof. by move/wo_chainW => Rtotal x xC; rewrite -[R x x]orbb Rtotal. Qed.

Lemma wo_chain_antisymmetric (T : eqType) R C : @wo_chain T R C -> {in C &, antisymmetric R}.
Proof.
have ne_cons x s: nonempty [mem x :: s : seq T] by exists x; apply: mem_head.
have all_mem s: all [mem s : seq T] s by apply/allP.
move/[dup]/wo_chainW => Rtotal /[dup]/wo_chain_reflexive Rxx Rwo x y xC yC.
have /Rwo[] := ne_cons x [::y]; first exact/allP/and3P.
move=> z [_ Uz] /andP[Rxy Ryx]; have /and3P[xy_x xy_y _] := all_mem [:: x; y].
by rewrite -(Uz x) ?(Uz y); split=> //; apply/allP; rewrite /= (Rxy, Ryx) Rxx.
Qed.

(******************************************************************************)

Section Zorn.

Lemma Zorn's_lemma (T : eqType) (R : rel T) (S : {pred T}) :
  {in S, reflexive R} -> {in S & &, transitive R} ->
  {in <= S, forall C, wo_chain R C -> exists2 z, z \in S & upper_bound R C z} ->
  {z : T | z \in S & {in S, maximal R z}}.
Proof.
suffices{T R S} Zorn (T : eqType) (R : rel T) (Well := wo_chain R) :
    preorder R -> (forall C, Well C -> {z | upper_bound R C z}) ->
  {z | maximal R z}.
- move=> Rxx Rtr UBch; pose T1 := {x | x \in S}.
  have S_T1 (u : T1): val u \in S by case: u.
  have [|C1 chC1|u maxT1u] := Zorn T1 (relpre val R); last 1 first.
  - by exists (val u) => // x Sx Rux; apply: (maxT1u (Sub x Sx)).
  - by split=> [x|y x z]; [apply: Rxx | apply: Rtr].
  pose C := [pred x | oapp (mem C1) false (insub x)].
  have sC1C u: u \in C1 -> val u \in C by rewrite inE valK.
  have memC x: x \in C -> {u | u \in C1 & val u = x}.
    by rewrite inE; case: insubP => //= u _ <-; exists u.
  apply/cid; suffices /UBch[_ /memC[u _ <-]//|z Sz ubCz]: wo_chain R C.
    by exists (Sub z Sz) => u C1u; apply/ubCz/sC1C.
  move=> A sAC [x0 Ax0].
  have [||w [[C1w minC1w] Uw]] := chC1 [preim val of A].
  - by move=> v /sAC; rewrite inE valK.
  - by have /sAC/memC[u0 C1u0 Du0] := Ax0; exists u0; rewrite inE Du0.
  exists (val w); do ?[split] => // [y Ay | y [Ay minAy]].
    by case/sAC/memC: Ay (Ay) => v C1v <-; apply: minC1w.
  have /sAC/memC[v C1v Dv] := Ay; rewrite (Uw v) //.
  by split=> [|u Au]; rewrite ?inE /= Dv // minAy.
case=> Rxx Rtr UBch; absurd_not=> nomaxR.
pose R' := [rel x y | R x y && ~~ R y x].
have{nomaxR} /all_sig[f fP] C: {z | Well C -> upper_bound R' C z}.
  have /UBch[z0 _]: Well pred0 by move=> A sA0 [x /sA0].
  have [/UBch[y RCy]|] := asboolP (Well C); last by exists z0.
  have [z Ryz notRzy] := nomaxR y; exists z => _ x /RCy-Rxy /=.
  by rewrite (Rtr y) //=; contra: notRzy => /Rtr->.
have notCf C: Well C -> f C \notin C.
  by move/fP=> R'Cf; apply/negP=> /R'Cf/=; rewrite Rxx ?andbF.
pose f_ind X := Well X /\ {in X, forall x, f [pred y in X | ~~ R x y] = x}.
pose init_seg (X Y : {pred T}) :=
  {subset X <= Y} /\ {in Y, forall y, y \notin X -> upper_bound R X y}.
have init_total Y Z: f_ind Y -> f_ind Z -> {init_seg Y Z} + {init_seg Z Y}.
  move=> indY indZ; pose iniYZ X := `[< init_seg X Y /\ init_seg X Z >].
  pose I x := `[< exists2 X, X \in iniYZ & x \in X >]; pose I1 := [predU1 f I & I].
  have [iIY iIZ]: init_seg I Y /\ init_seg I Z.
    split; split=> [x /asboolP[X /asboolP[[sXY _] [sXZ _]]]|]; try by move: (x).
      move=> y Yy /asboolP-I'y x /asboolP[X iXYZ Xx]; have /asboolP[[_ RXY] _] := iXYZ.
      by rewrite RXY //; contra: I'y; exists X.
    move=> z Zz /asboolP-I'z x /asboolP[X iXYZ Xx]; have /asboolP[_ [_ RXZ]] := iXYZ.
    by rewrite RXZ //; contra: I'z; exists X.
  have maxI: {in iniYZ, forall X, {subset X <= I}}; last clearbody I.
    by move=> X sXYZ x Xx; apply/asboolP; exists X.
  have Ich: Well I by have [Ych _] := indY; apply: sub_within Ych; case: iIY.
  generally have iI1, iI1Y: Y indY iIY {iniYZ maxI} / {I = Y} + {init_seg I1 Y}.
    have [[Ych fY] [sIY RIY]] := (indY, iIY).
    have /wo_chain_antisymmetric RYanti := Ych.
    have [sYI | /notP-ltIY] := asboolP {subset Y <= I}; [left | right].
      by apply/funext=> y; apply/idP/idP=> [/sIY | /sYI].
    have{ltIY} /Ych[_ /andP[]//| z [[/andP/=[I'z Yz]]]]: nonempty [predD Y & I].
      by have [y] := ltIY; exists y; apply/andP.
    move=> minYz _; suffices Dz: f I = z.
      rewrite /I1 Dz; do 2?[split] => // [x /predU1P[->|/sIY] // | y Yy].
      by case/norP=> /= z'y I'y x /predU1P[->|/RIY->//]; apply/minYz/andP.
    rewrite -(fY z Yz); congr f; apply/esym/funext=> x /=.
    apply/idP/idP=> [/andP[Yx] | Ix]; first by contra=> I'x; apply/minYz/andP.
    have Yx := sIY x Ix; rewrite Yx /=; contra: (I'z) => Rzx.
    by rewrite (RYanti z x) // Rzx RIY.    
  case: iI1Y {iI1}(iI1 Z) => [<- _| iI1Y [||<-|iI1Z]//]; [by left | by right |].
  by case/notCf/negP: Ich; apply/(maxI I1); [apply/asboolP|apply/predU1l].
pose U x := `[< exists2 X, x \in X & f_ind X >].
have Umax X: f_ind X -> init_seg X U.
  move=> indX; split=> [x Xx | y]; first by apply/asboolP; exists X.
  case/asboolP=> Y Yy indY notXy x Xx.
  by have [[sYX _]|[_ ->//]] := init_total Y X indY indX; rewrite sYX in notXy.
have RUanti: {in U &, antisymmetric R}.
  move=> x y /asboolP[X Xx indX] /asboolP[Y Yy indY].
  without loss [sXY _]: x y X Y Xx Yy {indX} indY / init_seg X Y.
    move=> IH. 
    by case: (init_total X Y) => // {}/IH-IH; [|rewrite andbC] => /IH->.
  have [/wo_chain_antisymmetric RYanti _] := indY.
  by apply: RYanti => //; apply: sXY.
have Uch: Well U.
  apply: antisymmetric_wo_chain => // A sAU [x0 Ax0].
  have /sAU/asboolP[X Xx0 indX] := Ax0.
  pose B := [predI A & X]; have sBX: {subset B <= X} by move=> y /andP[].
  have [[Xch _] /Umax[sXU iXU]] := (indX, indX).
  have{x0 Ax0 Xx0} /Xch[//|z [[/andP[/= Az Xz] minBz] _]]: nonempty B.
    by exists x0; apply/andP.
  exists z; split=> // y Ay; have Uy := sAU y Ay.
  by have [Xy | /iXU->//] := boolP (y \in X); apply/minBz/andP.
pose U1 := [predU1 f U & U]; have notUfU: f U \notin U by apply: notCf.
suffices indU1: f_ind U1.
  by have [sU1U _] := Umax U1 indU1; rewrite sU1U ?inE ?eqxx in notUfU.
have RU1fU: upper_bound R U1 (f U) by move=> x /predU1P[-> // | /fP/andP[]] .
split=> [A sAU1 neA | x U1x].
  have [sAfU | {neA}/notP[x Ax fU'x]] := asboolP {subset A <= pred1 (f U)}.
    have AfU: f U \in A by have [x Ax] := neA; have /sAfU/eqP<- := Ax.
    by exists (f U); split=> [|y [/sAfU/eqP//]]; split=> // _ /sAfU/eqP->.
  have Ux: x \in U by case/sAU1/orP: Ax => // /idPn.
  pose B := [predI A & U]; have sBU: {subset B <= U} by move=> y /andP[].
  have /Uch[//|z [[/andP[/= Az Uz] minBz] _]]: nonempty B.
    by exists x; apply/andP.
  have{minBz} minAz: lower_bound R A z.
    move=> y Ay; case/sAU1/predU1P: (Ay) => [->|/= Uy]; first exact/RU1fU/sAU1.
    exact/minBz/andP.
  exists z; do ?[split] => // y [Ay minAy].
  have /sAU1/predU1P[Dy|Uy] := Ay; last by apply: RUanti; rewrite ?minAz ?minAy.
  by have /andP[_] := fP U Uch z Uz; rewrite -Dy minAy.
have /predU1P[-> | /asboolP[X Xx indX]] := U1x.
  congr f; apply/funext=> y; apply/idP/idP=> [|Uy]; last first.
     by rewrite !inE unfold_in -/(U y) Uy orbT; case/andP: (fP U Uch y Uy).
  by case/andP=> /predU1P[->|//]; rewrite Rxx.
have{indX} [[_ f_indX] /Umax[sXU iXU]] := (indX, indX).
rewrite -[RHS]f_indX //; congr f; apply/funext=> y; apply/andb_id2r=> notRyx.
apply/idP/idP=> [U1y | Xy]; last exact/predU1r/sXU.
by contra: notRyx => notXy; have /predU1P[->|/iXU->] := U1y; first apply/RU1fU.
Qed.

Theorem Hausdorff_maximal_principle T R (S C : {pred T}) :
  {in S, reflexive R} -> {in S & &, transitive R} -> chain R C -> {subset C <= S} ->
  {M : {pred T} |
    [/\ {subset C <= M}, {subset M <= S}
      & forall X, chain R X -> {subset M <= X} -> {subset X <= S} -> M = X]}.
Proof.
move=> Rxx Rtr Cch sCS.
pose CSch X := `[< [/\ chain R X, {subset C <= X} & {subset X <= S}] >].
pose Rch (X Y : {pred T}) := `[< {subset X <= Y} >].
have: {in CSch & &, transitive Rch}.
  by apply: in3W => X Y Z /asboolP-sXY /asboolP-sYZ; apply/asboolP=> x /sXY/sYZ.
have /Zorn's_lemma/[apply]: {in CSch, reflexive Rch} by move=> X _; apply/asboolP.
case=> [XX CSchXX XXwo | M /asboolP[Mch sCM sMS] maxM]; last first.
  exists M; split=> // X Xch sMX sXS.
  suffices /asboolP-sXM: Rch X M by apply/funext=> x; apply/idP/idP=> [/sMX|/sXM].
  by apply: maxM; apply/asboolP=> //; split=> // x /sCM/sMX.
move/(@wo_chainW {pred T}): XXwo => XXch.
without loss XX_C: XX CSchXX XXch / C \in XX.
  have CSchC: C \in CSch by apply/asboolP; split.
  have RchC_CSch X: X \in CSch -> Rch C X by case/asboolP=> _ sCX _; apply/asboolP.
  pose XX1 X := `[< X = C \/ X \in XX >].
  have CSchXX1: {subset XX1 <= CSch} by move=> X /asboolP[-> | /CSchXX].
  case/(_ XX1)=> // [||Z CSchZ ubZ]; first 2 [by apply/asboolP; left].
    move=> X Y /asboolP[-> /CSchXX1/RchC_CSch-> //| XX_X].
    by rewrite orbC => /asboolP[-> | /XXch->//]; rewrite RchC_CSch ?CSchXX.
  by exists Z => // X XX_X; apply/ubZ/asboolP; right.
pose D x := `[< exists2 X, X \in XX & x \in X >].
have sCD: {subset C <= D} by move=> x Cx; apply/asboolP; exists C.
have sDS: {subset D <= S} by move=> x /asboolP[X /CSchXX/asboolP[_ _ sXS] /sXS].
have in2D: {in D &, forall x y, exists X, [/\ X \in XX, x \in X & y \in X]}.
  move=> x y /asboolP[X XX_X Xx] /asboolP[Y XX_Y Yy]; have:= XXch X Y XX_X XX_Y.
  by case/orP=> [/asboolP/(_ x Xx)|/asboolP/(_ y Yy)]; [exists Y | exists X].
exists D => [|X XX_X]; last by apply/asboolP=> x Xx; apply/asboolP; exists X.
apply/asboolP; split=> //.
move=> x y xD /(in2D x)-/(_ xD) [X [/CSchXX/asboolP[Xch _ _] Xx Xy]].
exact: Xch.
Qed.

Theorem well_ordering_principle (T : eqType) : {R : rel T | well_order R}.
Proof.
have{T} [T ->]: {T1 : eqType | T = T1} by exists T.
pose srel := pred T * rel T : Type.
pose loc (R : srel) := [rel x y | [&& x \in R.1, y \in R.1 & R.2 x y]].
pose pwo (R : srel) := `[< wo_chain R.2 R.1 >].
pose init_seg (R S : srel) :=
  {in R.1 & S.1, forall x y, S.2 x y = (y \in R.1) ==> R.2 x y}.
pose initR R S := `[< {subset R.1 <= S.1} /\ init_seg R S >].
have initRR: reflexive initR by move=> R; apply/asboolP; split=> // x y _ ->.
have initRtr: transitive initR.
  move=> R2 R1 R3 /asboolP[D12 R12] /asboolP[D23 R23]; apply/asboolP.
  split=> [x /D12/D23// | x y D1x D3y]; rewrite R23 ?(D12 x) //.
  by case D2y: (y \in R2.1); [apply: R12 | rewrite (contraFF (D12 y))].
have: {in pwo & &, transitive initR} by apply: in3W.
have/Zorn's_lemma/[apply]: {in pwo, reflexive initR} by [].
case=> [C pwoC Cch | [D R] /asboolP/=pwoR maxR].
  have /(@wo_chainW ({pred T} * rel T)%type) {}Cch := Cch.
  pose D x := `[< exists2 S, S \in C & x \in S.1 >]; pose R x y := `[< exists2 S, S \in C & loc S x y >].
  exists (D, R).
    apply/asboolP=> /= X sXD [x Xx]; have /sXD/asboolP[R0 CR0 /= D0x] := Xx.
    have /pwoC/asboolP/=R0wo := CR0.
    have{x Xx D0x}: nonempty [predI X & R0.1] by exists x; apply/andP.
    case/R0wo=> [_ /andP[]// |z [[/andP/=[Xz D0z] min0z] _]].
    have{R0 CR0 R0wo D0z min0z} minXz: lower_bound R X z.
      move=> y Xy; have /sXD/asboolP[R1 /= CR1 D1y] := Xy.
      have /orP[/asboolP/=[D10 R10] | /asboolP/=[D01 R01]] := Cch _ _ CR1 CR0.
        by apply/asboolP; exists R0; rewrite //= D0z min0z ?inE ?Xy D10.
      apply/asboolP; exists R1; rewrite //= R01 ?D1y// D01//=.
      by apply/implyP=> D0y; apply/min0z/andP.
    exists z; split=> // y [{}/minXz/asboolP[R0 CR0 R0zy] minXy].
    case/minXy/asboolP: Xz => {minXy} R1 CR1 R1yz.
    without loss /asboolP[D01 R01]: y z R0 R1 CR0 CR1 R0zy R1yz / initR R0 R1.
      by move=> IH; have /orP[/(IH y z)-> | /(IH z y)-> ] := Cch _ _ CR0 CR1.
    have{R1yz R0zy} [/and3P[D1y D1z R1zy] /and3P[D0z D0y R0yz]] := (R1yz, R0zy).
    have /pwoC/asboolP/wo_chain_antisymmetric R1anti := CR1.
    by apply: R1anti => //; rewrite R1zy R01 // D0y R0yz.
  move=> R0 CR0; apply/asboolP; split=> [x D0x|]; first by apply/asboolP; exists R0.
  move=> x y D0x Dy; apply/asboolP/idP=> [[R1 CR1 /and3P[D1x D1y R1xy]] | R0xy].
    have /orP[/asboolP[_ R10] | /asboolP[_ <- //]] := Cch _ _ CR1 CR0.
    by apply/implyP=> D0y; rewrite R10 // D1y R1xy.
  case/asboolP: Dy => R1 CR1 D1y.
  have /orP[/asboolP[D10 _] | /asboolP[D01 R01]] := Cch _ _ CR1 CR0.
    by exists R0; rewrite //= D0x (implyP R0xy) D10.
  by exists R1; rewrite //= D1y D01 ?R01.
exists R; apply: withinT; apply: sub_within (pwoR) => z _; assume_not=> notDz.
pose Rz x := predU1 z (if x \in D then R x else pred0).
have /maxR/(_ _)/asboolP: ([predU1 z & D] : pred T, Rz : rel T) \in pwo.
  apply/asboolP=> X sXxD neX; pose XD := [predI X & D].
  have [{neX}/pwoR[_ /andP[]//|x] | sXz] := asboolP (nonempty XD); last first.
    have {}sXz x: x \in X -> x = z.
      move=> Xx; case/sXxD/predU1P: (Xx) => // Dx.
      by case: sXz; exists x; apply/andP.
    have [x Xx] := neX; exists x; have /sXz-eq_xz := Xx.
    by split=> [|_ [/sXz-> //]]; split=> // _ /sXz->; apply/predU1l.
  case=> -[/andP/=[Xx Dx] minXDx] Ux; exists x; split=> [|y [Xy minXy]].
    split=> // y Xy; have /sXxD/predU1P[-> | Dy] := Xy; first exact/predU1l.
    by rewrite /= Dx; apply/predU1r/minXDx/andP.
  have Dy: y \in D.
    have /minXy/= := Xx; case: ifP => // _ /idPn[].
    by rewrite negb_or andbT (memPn notDz).
  apply: Ux; split=> [|t /andP[/minXy]]; first exact/andP.
  by rewrite /= Dy => /predU1P[-> /idPn[]|].   
case=> [|/= -> //]; last exact/predU1l.
apply/asboolP; split=> [x|x y /= Dx]; first exact: predU1r.
rewrite Dx => /predU1P[-> | /= Dy]; first by rewrite eqxx (negPf notDz).
by rewrite Dy -implyNb (memPn notDz).
Qed.

End Zorn.
