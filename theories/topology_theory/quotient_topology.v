(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical.
Require Import topology_structure.

(**md**************************************************************************)
(* # quotient topology                                                        *)
(*                                                                            *)
(* ```                                                                        *)
(*          quotient_topology Q == the quotient topology corresponding to     *)
(*                                 quotient Q : quotType T where T has type   *)
(*                                 topologicalType                            *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Definition quotient_topology (T : Type) (Q : quotType T) : Type := Q.

Section quotients.
Local Open Scope quotient_scope.
Section unpointed.
Context {T : topologicalType} {Q0 : quotType T}.

Local Notation Q := (quotient_topology Q0).

HB.instance Definition _ := Quotient.copy Q Q0.
HB.instance Definition _ := [Sub Q of T by %/].
HB.instance Definition _ := [Choice of Q by <:].

Definition quotient_open U := open (\pi_Q @^-1` U).

Program Definition quotient_topologicalType_mixin :=
  @isOpenTopological.Build Q quotient_open _ _ _.
Next Obligation. by rewrite /quotient_open preimage_setT; exact: openT. Qed.
Next Obligation. by move=> ? ? ? ?; exact: openI. Qed.
Next Obligation. by move=> I f ofi; apply: bigcup_open => i _; exact: ofi. Qed.
HB.instance Definition _ := quotient_topologicalType_mixin.

Lemma pi_continuous : continuous (\pi_Q : T -> Q).
Proof. exact/continuousP. Qed.

Lemma quotient_continuous {Z : topologicalType} (f : Q -> Z) :
  continuous f <-> continuous (f \o \pi_Q).
Proof.
split => /continuousP /= cts; apply/continuousP => A oA; last exact: cts.
by rewrite comp_preimage; move/continuousP: pi_continuous; apply; exact: cts.
Qed.

Lemma repr_comp_continuous (Z : topologicalType) (g : T -> Z) :
  continuous g -> {homo g : a b / \pi_Q a == \pi_Q b :> Q >-> a == b} ->
  continuous (g \o repr : Q -> Z).
Proof.
move=> /continuousP ctsG rgE; apply/continuousP => A oA.
rewrite /open/= /quotient_open (_ : _ @^-1` _ = g @^-1` A); first exact: ctsG.
have greprE x : g (repr (\pi_Q x)) = g x by apply/eqP; rewrite rgE// reprK.
by rewrite eqEsubset; split => x /=; rewrite greprE.
Qed.

End unpointed.

Section pointed.
Context {T : ptopologicalType} {Q0 : quotType T}.
Local Notation Q := (quotient_topology Q0).
HB.instance Definition _ := isPointed.Build Q (\pi_Q point : Q).
End pointed.
End quotients.
