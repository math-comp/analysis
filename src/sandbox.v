(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import tuple bigop ssralg ssrnum ssrint matrix mxalgebra vector.
Require Import zmodp rat reals complex.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

(* -------------------------------------------------------------------- *)
(* complex.v requires that R is a rcfType for constructing R[i]         *)

(* -------------------------------------------------------------------- *)
Section ComplexLModType.
Variable R : rcfType.

Implicit Types c x y : R.
Implicit Types z e   : R[i].

Definition scalec c e :=
  let: a +i* b := e in (c * a) +i* (c * b).

Local Notation "z1 *:c z2" := (scalec z1 z2) (at level 40).

Lemma scalecA c1 c2 z:
  c1 *:c (c2 *:c z) = (c1 * c2) *:c z.
Proof. by case: z => a b /=; rewrite !mulrA. Qed.

Lemma scale1c z: 1 *:c z = z.
Proof. by case: z => a b /=; rewrite !mul1r. Qed.

Lemma scalecDr c z1 z2:
  c *:c (z1 + z2) = c *:c z1 + c *:c z2.
Proof. by case: z1 z2 => [a1 b1] [a2 b2] /=; rewrite !mulrDr; simpc. Qed.

Lemma scalecDl z c1 c2:
  (c1 + c2) *:c z = c1 *:c z + c2 *:c z.
Proof. by case: z => [a b] /=; rewrite !mulrDl; simpc. Qed.

Definition complex_lmodMixin :=
  LmodMixin scalecA scale1c scalecDr scalecDl.

Canonical complex_lmodType :=
  Eval hnf in LmodType R R[i] complex_lmodMixin.
End ComplexLModType.

(* -------------------------------------------------------------------- *)
Section Sandbox.
Variable R : rcfType.

Implicit Types c x y : R.
Implicit Types z e   : R[i].

Lemma complex_vectAxiom: Vector.axiom 2 R[i].
Proof.
  exists (fun z => \row_(i < 2) (tnth [tuple (Re z); (Im z)] i)).
  + move=> /= c [a1 b1] [a2 b2]; apply/matrixP=> /= i j.
    by rewrite !mxE {i}!(tnth_nth 0) /=; case: j=> [] [|[|]].
  + exists (fun (v : 'rV[R]_2) => v 0 0 +i* v 0 1).
      by case=> [a b]; rewrite !mxE !(tnth_nth 0).
    move=> v /=; apply/matrixP=> i j; rewrite !mxE.
    rewrite !(tnth_nth 0) !ord1; case: j=> [] [|[|]] //= lt.
      have /eqP->//: Ordinal lt == 0 by rewrite eqE.
      have /eqP->//: Ordinal lt == 1 by rewrite eqE.
Qed.

Definition complex_vectMixin :=
  VectMixin complex_vectAxiom.

Canonical Structure complex_vectType :=
  Eval hnf in VectType R R[i] complex_vectMixin.
End Sandbox.
