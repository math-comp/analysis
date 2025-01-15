(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import topology_structure.

(**md**************************************************************************)
(* # Connectedness                                                            *)
(* This file provides connected and its related notions.                      *)
(*                                                                            *)
(* ```                                                                        *)
(*                   connected A <-> the only non empty subset of A which is  *)
(*                                   both open and closed in A is A           *)
(*                  separated A B == the two sets A and B are separated       *)
(*          connected_component x == the connected component of point x       *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section connected_sets.
Variable T : topologicalType.
Implicit Types A B C D : set T.

Definition connected A :=
  forall B, B !=set0 -> (exists2 C, open C & B = A `&` C) ->
  (exists2 C, closed C & B = A `&` C) -> B = A.

Lemma connected0 : connected (@set0 T).
Proof. by move=> ? ? [? ?]; rewrite set0I. Qed.

Definition separated A B :=
  (closure A) `&` B = set0 /\ A `&` (closure B) = set0.

Lemma separatedC A B : separated A B = separated B A.
Proof. by rewrite /separated andC setIC (setIC _ B). Qed.

Lemma separated_disjoint A B : separated A B -> A `&` B = set0.
Proof.
move=> AB; rewrite predeqE => x; split => // -[Ax Bx].
by move: AB; rewrite /separated => -[<- _]; split => //; apply: subset_closure.
Qed.

Lemma connectedPn A : ~ connected A <->
  exists E : bool -> set T, [/\ forall b, E b !=set0,
    A = E false `|` E true & separated (E false) (E true)].
Proof.
rewrite -propeqE; apply: notLR; rewrite propeqE.
split=> [conE [E [E0 EU [E1 E2]]]|conE B B0 [C oC BAC] [D cD BAD]].
  suff : E true = A.
    move/esym/(congr1 (setD^~ (closure (E true)))); rewrite EU setDUl.
    have := @subset_closure _ (E true); rewrite -setD_eq0 => ->; rewrite setU0.
    by move/setDidPl : E2 => ->; exact/eqP/set0P.
  apply: (conE _ (E0 true)).
  - exists (~` (closure (E false))); first exact/closed_openC/closed_closure.
    rewrite EU setIUl.
    have /subsets_disjoint -> := @subset_closure _ (E false); rewrite set0U.
    by apply/esym/setIidPl/disjoints_subset; rewrite setIC.
  - exists (closure (E true)); first exact: closed_closure.
    by rewrite EU setIUl E2 set0U; exact/esym/setIidPl/subset_closure.
apply: contrapT => AF; apply: conE.
exists (fun i => if i is false then A `\` C else A `&` C); split.
- case=> /=; first by rewrite -BAC.
  apply/set0P/eqP => /disjoints_subset; rewrite setCK => EC.
  by apply: AF; rewrite BAC; exact/setIidPl.
- by rewrite setDE -setIUr setUCl setIT.
- split.
  + rewrite setIC; apply/disjoints_subset.
    rewrite -interiorC interiorEbigcup => x [? ?].
    by exists C => //; split=> //; rewrite setDE setCI setCK; right.
  + apply/disjoints_subset => y -[Ay Cy].
    rewrite -BAC BAD => /closureI[_]; move/closure_id : cD => <- Dy.
    by have : B y; [by rewrite BAD; split|rewrite BAC => -[]].
Qed.

Lemma connectedP A : connected A <->
  forall E : bool -> set T, ~ [/\ forall b, E b !=set0,
    A = E false `|` E true & separated (E false) (E true)].
Proof.
rewrite -propeqE forallNE; apply: notRL; rewrite propeqE; exact: connectedPn.
Qed.

Lemma connected_subset A B C : separated A B -> C `<=` A `|` B ->
  connected C -> C `<=` A \/ C `<=` B.
Proof.
move=> AB CAB; have -> : C = (C `&` A) `|` (C `&` B).
  rewrite predeqE => x; split=> [Cx|[] [] //].
  by have [Ax|Bx] := CAB _ Cx; [left|right].
move/connectedP/(_ (fun b => if b then C `&` B else C `&` A)) => /not_and3P[]//.
  by move/existsNP => [b /set0P/negP/negPn]; case: b => /eqP ->;
    rewrite !(setU0,set0U); [left|right]; apply: subIset; right.
case/not_andP => /eqP/set0P[x []].
- move=> /closureI[cCx cAx] [Cx Bx]; exfalso.
  by move: AB; rewrite /separated => -[] + _; apply/eqP/set0P; exists x.
- move=> [Cx Ax] /closureI[cCx cBx]; exfalso.
  by move: AB; rewrite /separated => -[] _; apply/eqP/set0P; exists x.
Qed.

Lemma connected1 x : connected [set x].
Proof.
move=> X [y +] [O Oopen XO] [C Cclosed XC]; rewrite XO.
by move=> [{y}-> Ox]; apply/seteqP; split=> y => [[->//]|->].
Qed.
Hint Resolve connected1 : core.

Lemma bigcup_connected I (A : I -> set T) (P : I -> Prop) :
  \bigcap_(i in P) (A i) !=set0 -> (forall i, P i -> connected (A i)) ->
  connected (\bigcup_(i in P) (A i)).
Proof.
move=> [c AIc] cA; have [[i Pi]|] := pselect (exists i, P i); last first.
  move/forallNP => P0.
  rewrite (_ : P = set0) ?bigcup_set0; first exact: connected0.
  by rewrite predeqE => x; split => //; exact: P0.
apply/connectedP => [E [E0 EU sE]].
wlog E0c : E E0 EU sE / E false c.
  move=> G; have : (\bigcup_(i in P) A i) c by exists i => //; exact: AIc.
  rewrite EU => -[E0c|E1c]; first exact: G.
  by apply: (G (E \o negb)) => //;
    [case => /=|rewrite EU setUC|rewrite separatedC].
move: (E0 true) => /set0P/eqP; apply.
have [/eqP //|/set0P[d E1d]] := boolP (E true == set0).
have : \bigcup_(i in P) A i `<=` E false.
  suff AE : forall i, P i -> A i `<=` E false by move=> x [j ? ?]; exact: (AE j).
  move=> j Pj.
  move: (@connected_subset _ _ (A j) sE).
  rewrite -EU => /(_ (bigcup_sup _) (cA _ Pj)) [//| | AjE1]; first exact.
  exfalso; have E1c := AjE1 _ (AIc _ Pj).
  by move/separated_disjoint : sE; apply/eqP/set0P; exists c.
rewrite EU subUset => -[_] /(_ _ E1d) E0d; exfalso.
by move/separated_disjoint : sE; apply/eqP/set0P; exists d.
Qed.

Lemma connectedU A B : A `&` B !=set0 -> connected A -> connected B ->
  connected (A `|` B).
Proof.
move=> [x [Ax Bx]] Ac Bc; rewrite -bigcup2inE; apply: bigcup_connected.
  by exists x => //= -[|[|[]]].
by move=> [|[|[]]].
Qed.

Lemma connected_closure A : connected A -> connected (closure A).
Proof.
move=> ctdA U U0 [C1 oC1 C1E] [C2 cC2 C2E]; rewrite eqEsubset C2E; split => //.
suff : A `<=` U.
  move/closure_subset; rewrite [_ `&` _](iffLR (closure_id _)) ?C2E//.
  by apply: closedI => //; exact: closed_closure.
rewrite -setIidPl; apply: ctdA.
- move: U0; rewrite C1E => -[z [clAx C1z]]; have [] := clAx C1.
    exact: open_nbhs_nbhs.
  by move=> w [Aw C1w]; exists w; rewrite setIA (setIidl (@subset_closure _ _)).
- by exists C1 => //; rewrite C1E setIA (setIidl (@subset_closure _ _)).
- by exists C2 => //; rewrite C2E setIA (setIidl (@subset_closure _ _)).
Qed.

Definition connected_component (A : set T) (x : T) :=
  \bigcup_(A in [set C : set T | [/\ C x, C `<=` A & connected C]]) A.

Lemma component_connected A x : connected (connected_component A x).
Proof. by apply: bigcup_connected; [exists x => C []|move=> C []]. Qed.

Lemma connected_component_sub A x : connected_component A x `<=` A.
Proof. by move=> y [B [_ + _]] => /[apply]. Qed.

Lemma connected_component_id A x :
  A x -> connected A -> connected_component A x = A.
Proof.
move=> Ax Ac; apply/seteqP; split; first exact: connected_component_sub.
by move=> y Ay; exists A => //; split.
Qed.

Lemma connected_component_out A x :
  ~ A x -> connected_component A x = set0.
Proof. by move=> NAx; rewrite -subset0 => y [B [/[swap]/[apply]]]. Qed.

Lemma connected_component_max A B x : B x -> B `<=` A ->
  connected B -> B `<=` connected_component A x.
Proof. by move=> Bx BA Bc y By; exists B. Qed.

Lemma connected_component_refl A x : A x -> connected_component A x x.
Proof. by move=> Ax; exists [set x] => //; split => // _ ->. Qed.

Lemma connected_component_cover A :
  \bigcup_(A in connected_component A @` A) A = A.
Proof.
apply/predeqP => x; split=> [[B [y By <- /connected_component_sub//]]|Ax].
by exists (connected_component A x) => //; apply: connected_component_refl.
Qed.

Lemma connected_component_sym A x y :
  connected_component A x y -> connected_component A y x.
Proof. by move=> [B [*]]; exists B. Qed.

Lemma connected_component_trans A y x z :
    connected_component A x y -> connected_component A y z ->
  connected_component A x z.
Proof.
move=> [B [Bx BA Ac Ay]] [C [Cy CA Cc Cz]]; exists (B `|` C); last by right.
by split; [left | rewrite subUset | apply: connectedU=> //; exists y].
Qed.

Lemma same_connected_component A x y : connected_component A x y ->
  connected_component A x = connected_component A y.
Proof.
move=> Axy; apply/seteqP; split => z; apply: connected_component_trans => //.
by apply: connected_component_sym.
Qed.

Lemma component_closed A x : closed A -> closed (connected_component A x).
Proof.
move=> clA; have [Ax|Ax] := pselect (A x); first last.
  by rewrite connected_component_out //; exact: closed0.
rewrite closure_id eqEsubset; split; first exact: subset_closure.
move=> z Axz; exists (closure (connected_component A x)) => //.
split; first exact/subset_closure/connected_component_refl.
  rewrite [X in _ `<=` X](closure_id A).1//.
  by apply: closure_subset; exact: connected_component_sub.
by apply: connected_closure; exact: component_connected.
Qed.

Lemma clopen_separatedP A : clopen A <-> separated A (~` A).
Proof.
split=> [[oA cA]|[] /[!(@disjoints_subset T)] /[!(@setCK T)] clAA AclA].
  rewrite /separated -((closure_id A).1 cA) setICr ; split => //.
  by rewrite -((closure_id _).1 (open_closedC oA)) setICr.
split; last by rewrite closure_id eqEsubset; split => //; exact: subset_closure.
by rewrite -closedC closure_id eqEsubset; split;
  [exact: subset_closure|exact: subsetCr].
Qed.

End connected_sets.

Arguments connected {T}.
Arguments connected_component {T}.
