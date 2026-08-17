From HB Require Import structures.
From Stdlib Require Import Bool.
From mathcomp Require Import all_boot all_order.
From mathcomp Require Import ssralg ssrnum ssrint interval finmap.
From mathcomp Require Import perm fingroup interval_inference contra.
From mathcomp Require Import reals real_interval.
From mathcomp Require Import mathcomp_extra boolp classical_sets .
From mathcomp Require Import functions cardinality fsbigop set_interval.
From mathcomp Require Import topology normedtype sequences.

(**md**************************************************************************)
(* # Absolute Continuity                                                      *)
(* ```                                                                        *)
(*        abs_cont a b f  == the function f : R -> R is absolutely continuous *)
(*                           over [a, b]                                      *)
(*   abs_cont_order a b f == equivalent definition of abs_cont where the      *)
(*                           (non-overlapping) intervals forming the          *)
(*                           subdivision or ordered                           *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section absolute_continuity_def.
Context {R : realType}.

Definition abs_cont (a b : R) (f : R -> R) := forall e : {posnum R},
  exists d : {posnum R}, forall n (B : nat -> R * R),
    [/\ (forall i, (i < n)%N ->
          (B i).1 < (B i).2 /\ `](B i).1, (B i).2[ `<=` `[a, b]),
        trivIset `I_n (fun i => `](B i).1, (B i).2[%classic) &
        \sum_(k < n) ((B k).2 - (B k).1) < d%:num] ->
        \sum_(k < n) (f (B k).2 - f ((B k).1)) < e%:num.

Definition abs_cont_order (a b : R) (f : R -> R) := forall e : {posnum R},
  exists d : {posnum R}, forall n (B : nat -> R * R),
    [/\ (forall i, (i < n)%N ->
          ((B i).1 < (B i).2 /\ `](B i).1, (B i).2[ `<=` `[a, b])),
        (forall i j : 'I_n, (i < j)%N -> (B i).2 <= (B j).1),
        trivIset `I_n (fun i => `](B i).1, (B i).2[%classic) &
        \sum_(k < n) ((B k).2 - (B k).1) < d%:num] ->
        \sum_(k < n) (f (B k).2 - f ((B k).1)) < e%:num.

End absolute_continuity_def.

Section abs_contP.
Context {R : realType}.
Let disjoint_itv_le (a b c d : R) :
 a < b -> c < d ->
  `]a, b[%classic `&` `]c, d[%classic = set0 -> b <= c \/ d <= a.
Proof.
move=> ab cd abcd.
rewrite -implyNp; move/negP; rewrite -ltNge leNgt => cb; apply/negP => ad.
move: abcd; rewrite -subset0; have [ac|ac] := lerP a c; have [bd|bd] := lerP b d.
- move/(_ ((c + b) / 2)); apply; split => /=; rewrite in_itv/=.
    by rewrite (le_lt_trans ac)/= ?midf_lt.
  by rewrite (lt_le_trans _ bd)/= ?midf_lt.
- move/(_ ((c + d) / 2)); apply; split => /=; rewrite in_itv/= ?midf_lt//.
  by rewrite (le_lt_trans ac) ?(lt_trans _ bd) ?midf_lt.
- move/(_ ((a + b) / 2)); apply; split => /=; rewrite in_itv/= ?midf_lt//.
  by rewrite (lt_trans ac) ?(lt_le_trans _ bd) ?midf_lt.
- move/(_ ((a + d) / 2)); apply; split => /=; rewrite in_itv/=.
    by rewrite (lt_trans _ bd) ?midf_lt.
  by rewrite (lt_trans ac) ?midf_lt.
Qed.

Let lt_itv (B : (R * R)^nat) (i j : nat) := (i == j) || ((B i).2 <= (B j).1).

Lemma abs_contP (a b : R) (f : R -> R) : abs_cont a b f <-> abs_cont_order a b f.
Proof.
split=> [h e|h e].
  by have {h}[d h] := h e; exists d => n B [BS B21 tB] Bd; exact: (h n B).
have {h}[d h] := h e; exists d => n B [BS tB Bd].
pose ordered_indices := sort (lt_itv B) (iota 0 n).
pose g_nat : nat -> nat := nth 0 ordered_indices.
have g_nat_ub (i : 'I_n) : (g_nat i < n)%N.
  apply/(@all_nthP _ [pred x | x < n]%N).
    by apply/allP => x /=; rewrite mem_sort mem_iota add0n leq0n.
  by rewrite size_sort size_iota.
pose g : {ffun 'I_n -> 'I_n} := [ffun i => Ordinal (g_nat_ub i)].
have g_nat_inj : {in gtn n &, injective g_nat}.
  move=> /= i j /[!inE] ni nj.
  rewrite /g_nat /= /ordered_indices.
  have : uniq ordered_indices by rewrite sort_uniq// iota_uniq.
  move/uniqP => /(_ 0) /[apply].
  rewrite !inE !size_sort !size_iota.
  exact.
have g_inj : injectiveb g.
  apply/injectiveP => /= i j.
  rewrite /g /= !ffunE.
  move/(congr1 val)/g_nat_inj.
  rewrite !inE => /(_ (ltn_ord i) (ltn_ord j)) ij.
  exact/val_inj.
pose Bg : 'I_ n -> R * R := B \o (fun x => g x).
pose Bg_nat (i : nat) : R * R := match Bool.bool_dec (i < n)%N true with
  | left H => Bg (@Ordinal n _ H)
  | _ => B 0
  end.
have nbBg_nat (i j : 'I_n ) : (i < j)%N -> (Bg_nat i).2 <= (Bg_nat j).1.
  move=> ij.
  rewrite /Bg_nat; case: Bool.bool_dec => [ni|]; last by rewrite ltn_ord.
  case: Bool.bool_dec => [nj|]; last by rewrite ltn_ord.
  rewrite /Bg /=.
  suff: lt_itv B (g_nat i) (g_nat j).
    rewrite /lt_itv => /predU1P[|].
      move/injectiveP in g_inj.
      move/g_nat_inj.
      rewrite !inE ni nj => /(_ erefl erefl) ji.
      by rewrite ji ltnn in ij.
    by rewrite /g/= !ffunE/=; exact.
  have := @sorted_ltn_nth_in _ _ (lt_itv B).
  apply => //.
  - move=> x y z.
    rewrite !mem_sort !mem_iota !add0n !leq0n/= => xn yn zn.
    rewrite /lt_itv => /predU1P[->|yx].
      move=> /predU1P[->|->].
        by rewrite eqxx.
      by rewrite orbT.
    move=> /predU1P[<-|xz].
      by rewrite yx orbT.
    have [->//|yz/=] := eqVneq y z.
    rewrite (le_trans yx)// (le_trans _ xz)// ltW//.
    exact: (BS _ xn).1.
  - apply: (@sort_sorted_in _ [pred x | x < n]%N).
      move=> x y; rewrite !inE => xn yn.
      rewrite /lt_itv; have [//|/= xy] := eqVneq x y.
      apply/orP/disjoint_itv_le.
      - exact: (BS _ xn).1.
      - exact: (BS _ yn).1.
      - by move/trivIsetP : tB => /(_ (Ordinal xn) (Ordinal yn)); exact.
    by apply/allP => /= y; rewrite mem_iota leq0n.
  - by rewrite inE size_sort size_iota.
  - by rewrite inE size_sort size_iota.
pose permg : {perm 'I_n} := Perm g_inj.
have K : \sum_(k < n) (f (B k).2 - f (B k).1) =
     \sum_(k < n) (f (Bg_nat k).2 - f (Bg_nat k).1).
  rewrite (reindex_onto permg permg^-1%g)//=; last by move=> i _; rewrite permKV.
  apply/eq_big.
    by move=> i; rewrite /= permK eqxx.
  move=> i _.
  rewrite /Bg_nat; case: Bool.bool_dec => /=; last by rewrite (ltn_ord i).
  move=> ni.
  rewrite /Bg/= /permg/=.
  suff : Perm g_inj i = g (Ordinal ni) by move=> <-.
  rewrite unlock/=.
  rewrite (_ : Ordinal ni = i)//.
  exact/val_inj.
rewrite K; apply: h; split => //.
- move=> i ni; split.
    rewrite /Bg_nat; case: Bool.bool_dec => //= ni'.
    rewrite /Bg/=.
    exact: (BS _ _).1.
  rewrite /Bg_nat; case: Bool.bool_dec => //= ni'.
  rewrite /Bg/=.
  exact: (BS _ _).2.
- apply/trivIsetP => /= i j ni nj ij.
  rewrite /Bg_nat; case: Bool.bool_dec => //= ni'.
  rewrite /Bg/=; case: Bool.bool_dec => //= nj'.
  move/trivIsetP : tB; apply => //=.
  apply: contra ij => /eqP.
  rewrite {permg}.
  move: g_inj => /injectiveP g_inj H.
  have /(_ _)/(congr1 val)/eqP := g_inj (Ordinal ni') (Ordinal nj').
  apply.
  exact/val_inj.
- rewrite [ltLHS](_ : _ = \sum_(k < n) ((B k).2 - (B k).1))//.
  rewrite [RHS](reindex_onto permg permg^-1%g)//=; last by move=> i _; rewrite permKV.
  apply/eq_big.
    by move=> i; rewrite /= permK eqxx.
  move=> i _.
  rewrite /Bg_nat; case: Bool.bool_dec => [ni|]; last by rewrite (ltn_ord _).
  rewrite /Bg/= /permg/=.
  suff : Perm g_inj i = g (Ordinal ni) by move=> <-.
  rewrite unlock/=.
  rewrite (_ : Ordinal ni = i)//.
  exact/val_inj.
Qed.

End abs_contP.
