(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice order.
From mathcomp Require Import ssrnat seq fintype bigop div prime path finmap.
From mathcomp Require Import ssralg ssrnum ssrint rat.
Require Import boolp classical_sets.

(******************************************************************************)
(*                              Cardinality                                   *)
(*                                                                            *)
(* This file provides an account of cardinality properties of classical sets. *)
(* This includes standard results of naive set theory such as the Pigeon Hole *)
(* principle, the Cantor-Bernstein Theorem, or lemmas about the cardinal of   *)
(* nat, nat * nat, and rat.                                                   *)
(*                                                                            *)
(* The contents of this file should not be considered as definitive because   *)
(* it establishes too little connections with MathComp: finite sets are       *)
(* defined using finmap's fsets but countability does not build on countType. *)
(* Improvement is explored in PR #83.                                         *)
(*                                                                            *)
(*    surjective A B f == the function f whose domain is the set A and its    *)
(*                        codomain is the set B is surjective                 *)
(* set_bijective A B f == the function f whose domain is the set A and its    *)
(*                        codomain is the set B is bijective                  *)
(*      inverse t0 A f == the inverse function induced by f on its codomain;  *)
(*                        the set A is the domain of f; t0 is an arbitrary    *)
(*                        element in the support type of A (not necessarily   *)
(*                        belonging to A)                                     *)
(*                `I_n == the set of natural numbers less than n, i.e.,       *)
(*                        [set k | k < n]                                     *)
(*             A #<= B == the cardinal of A is less than or equal to the      *)
(*                        cardinal of B                                       *)
(*              A #= B == A and B have the same cardinal                      *)
(*         countable A == the cardinality of A is less than or equal to the   *)
(*                        one of the set of natural numbers, i.e.,            *)
(*                        A #<= @setT nat                                     *)
(*        set_finite A == there is finite set F (of type {fset _}) s.t. A = F *)
(*                        various lemmas about set_finite: existence of a     *)
(*                        bijection with `I_n, finiteness of a preimage by an *)
(*                        injective function, finiteness of surjective image, *)
(*                        finiteness of difference, union, etc.               *)
(* infinite_nat_subset_countable == a non-empty, not finite set of natural    *)
(*                        has the same cardinal as the full set               *)
(*     enumeration S e == the function e : nat -> T is an enumeration of the  *)
(*                        set S, i.e., S = e @` setT                          *)
(*  enum_wo_rep nfA Ae == with Ae : enumeration A e, nfA : ~ set_finite A     *)
(*                        enumeration without repetition of A                 *)
(*         pair_of_rat == injection from rat to nat * nat                     *)
(*          nat_of_rat == injection from rat to nat                           *)
(*          rat_of_nat == cancel function for nat_of_rat                      *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "'`I_' n" (at level 8, n at level 2, format "'`I_' n").
Reserved Notation "A '#<=' B" (at level 79, format "A  '#<='  B").

Import Order.TTheory GRing.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(* TODO: move *)
Lemma in_inj_comp A B C (f : B -> A) (h : C -> B) (P : pred B) (Q : pred C) :
  {in P &, injective f} -> {in Q &, injective h} -> {homo h : x / Q x >-> P x} ->
  {in Q &, injective (f \o h)}.
Proof.
by move=> Pf Qh QP x y xQ yQ xy; apply Qh => //; apply Pf => //; apply QP.
Qed.

Lemma enum0 : enum 'I_0 = [::].
Proof. by apply/eqP; rewrite -size_eq0 size_enum_ord. Qed.

Lemma enum_recr n : enum 'I_n.+1 =
  rcons (map (widen_ord (leqnSn _)) (enum 'I_n)) ord_max.
Proof.
apply (@eq_from_nth _ ord0) => /= [|i].
  by rewrite size_rcons size_map 2!size_enum_ord.
rewrite size_enum_ord leq_eqVlt => /orP[/eqP[->{i}]|].
  rewrite nth_rcons size_map size_enum_ord ltnn eqxx.
  by rewrite (@nth_ord_enum _ _ ord_max).
rewrite ltnS => ni;rewrite nth_rcons /= size_map size_enum_ord ni.
apply val_inj => /=; rewrite nth_enum_ord ?(ltn_trans ni)//.
case: n => // n in ni *.
by rewrite (@nth_map _ ord0) ?size_enum_ord //= nth_enum_ord.
Qed.

Lemma eq_set0_nil (T : eqType) (S : seq T) :
  ([set x | x \in S] == set0) = (S == [::]).
Proof.
apply/eqP/eqP=> [|->]; rewrite predeqE //; case: S => // h t /(_ h).
by rewrite /mkset mem_head => -[/(_ erefl)].
Qed.

Lemma eq_set0_fset0 (T : choiceType) (S : {fset T}) :
  ([set x | x \in S] == set0) = (S == fset0).
Proof. by rewrite eq_set0_nil. Qed.
(* /TODO: move *)

Lemma image_nat_maximum n (f : nat -> nat) :
  (exists i, i <= n /\ forall j, j <= n -> f j <= f i)%N.
Proof.
elim: n => [|n [j [jn1 nfj]]]; first by exists 0%N; split => //; case.
have [fn1fj|fjfn1] := leP (f n.+1) (f j).
  exists j; split=> [|i]; first by rewrite (leq_trans jn1).
  by rewrite leq_eqVlt => /orP[/eqP -> //|]; rewrite ltnS; apply nfj.
have fmax : (forall i, i <= n -> f n.+1 > f j /\ f j >= f i)%N.
  by move=> i ni; split => //; exact: nfj ni.
exists n.+1; split => // k; rewrite leq_eqVlt ltnS => /orP[/eqP-> //|].
by move/fmax => [_ /leq_trans]; apply; exact/ltnW.
Qed.

Lemma fset_nat_maximum (A : {fset nat}) : A != fset0 ->
  (exists i, i \in A /\ forall j, j \in A -> j <= i)%nat.
Proof.
move=> A0; move/fset0Pn : (A0) => [a Aa].
set f := nth a (enum_fset A).
have [i [iA H]] := image_nat_maximum (#|` A|.-1)%fset f.
exists (f i); split => [|j Aj].
  by rewrite /f mem_nth // -(@prednK #|` A|) ?ltnS // cardfs_gt0.
have [k [kA <-]] : (exists k, k < #|` A| /\ f k = j)%N.
  by exists (index j A); rewrite index_mem /f nth_index.
by rewrite H //; move: kA; rewrite -(@prednK #|` A|) // cardfs_gt0.
Qed.

Definition surjective aT rT (A : set aT) (B : set rT) (f : aT -> rT) :=
  forall u, B u -> exists t, A t /\ u = f t.

Section surjective_lemmas.
Variables aT rT : Type.
Implicit Types (A : set aT) (B : set rT) (f : aT -> rT).

Lemma surjective_id T : surjective setT setT (@id T).
Proof. by move=> t _; exists t. Qed.

Lemma surjective_set0 B f : surjective set0 B f -> B = set0.
Proof. by move=> Bf; rewrite predeqE => u; split => // /Bf [t []]. Qed.

Lemma surjective_image A f : surjective A (f @` A) f.
Proof. by move=> u [t At <-{u}]; exists t. Qed.

Lemma surjective_image_eq0 A B f : f @` A `<=` B ->
  B `\` f @` A = set0 -> surjective A B f.
Proof.
move=> ? BfA u Bu; have [[t]|fAu] := pselect ((f @` A) u); first by exists t.
by move: BfA; rewrite predeqE => /(_ u)[] /(_ (conj Bu fAu)).
Qed.

Lemma surjectiveE f A B :
  surjective A B f = (B `<=` f @` A).
Proof. by rewrite propeqE; split=> fP y /fP[x] => [[]|]; exists x. Qed.

Lemma surj_image_eq B A f :
 f @` A `<=` B -> surjective A B f -> f @` A = B.
Proof. by move=> fAB; rewrite surjectiveE eqEsubset => BfA. Qed.

Lemma can_surjective g f (A : {pred aT}) (B : {pred rT}) :
    {in B, {on A, cancel g & f}} -> {homo g : x / x \in B >-> x \in A} ->
  surjective A B f.
Proof.
move=> gK gBA y By; suff : A (g y) by exists (g y); rewrite gK ?inE.
by have := gBA y; apply.
Qed.

End surjective_lemmas.
Arguments can_surjective {aT rT} g [f A B].

Lemma surjective_comp T1 T2 T3 (A : set T1) (B : set T2) (C : set T3) f g:
  surjective A B f -> surjective B C g -> surjective A C (g \o f).
Proof.
move=> ABf BCg v Cv.
have [u [Bu vgu]] := BCg _ Cv; have [t [At uft]] := ABf _ Bu.
by exists t; split => //; rewrite vgu uft.
Qed.

Definition set_bijective aT rT (A : set aT) (B : set rT) (f : aT -> rT) :=
  [/\ {in A &, injective f}, f @` A `<=` B & surjective A B f].

Section set_bijective_lemmas.
Variables aT rT : Type.
Implicit Types (A : set aT) (B : set rT) (f : aT -> rT).

Lemma inj_of_bij A B f : set_bijective A B f -> {in A &, injective f}.
Proof. by case. Qed.

Lemma sub_of_bij A B f : set_bijective A B f -> f @` A `<=` B.
Proof. by case. Qed.

Lemma sur_of_bij A B f : set_bijective A B f -> surjective A B f.
Proof. by case. Qed.

Lemma set_bijective1 A B f g : {in A, f =1 g} ->
  set_bijective A B f -> set_bijective A B g.
Proof.
move=> fg bij_f; split.
- by move=> i j Ai Aj; rewrite -fg // -fg // => /(inj_of_bij bij_f); apply.
- move=> u [t At]; rewrite -fg ?in_setE// => <-{u}; apply: (sub_of_bij bij_f).
  by exists t.
- move=> u Au; have [t [At uft]] := (sur_of_bij bij_f) _ Au.
  by exists t; split => //; rewrite -fg// in_setE.
Qed.

Lemma set_bijective_image A f :
  {in A &, injective f} -> set_bijective A (f @` A) f.
Proof. by move=> fi; split => // u [t At <-{u}]; exists t. Qed.

Lemma set_bijective_subset A B f :
  set_bijective A B f -> forall B0, B0 `<=` B ->
  set_bijective ((f @^-1` B0) `&` A) B0 f.
Proof.
move=> bij_f B0 B0B; split.
- move=> i j; rewrite !in_setE /preimage => -[B0fi Ai] [B0fj Aj].
  by move/(inj_of_bij bij_f) => -> //; rewrite in_setE //.
- by move=> u [t]; rewrite /preimage => -[B0ft At] <-{u}.
- move=> u B0u.
  have [t [At uft]] := (sur_of_bij bij_f) _ (B0B _ B0u).
  by exists t; split => //; split => //; rewrite /preimage /mkset -uft.
Qed.

End set_bijective_lemmas.

Lemma set_bijective_comp T1 T2 T3 (A : set T1) (B : set T2) (C : set T3) f g :
  set_bijective A B f -> set_bijective B C g -> set_bijective A C (g \o f).
Proof.
move=> [fi fAB fs] [gi gBC gs]; split.
- apply (in_inj_comp gi fi) => t; rewrite 2!in_setE => At.
  by apply fAB; exists t.
- by move=> v [t At <-{v}]; apply gBC; exists (f t) => //; apply fAB; exists t.
- exact (surjective_comp fs gs).
Qed.

Definition inverse (T : choiceType) (t0 : T) U (A : set T) (f : T -> U) :=
  fun t => xget t0 ((f @^-1` [set t]) `&` A).

Section inverse_lemmas.
Variables (aT : choiceType) (t0 : aT) (rT : Type).
Implicit Types (A : set aT) (B : set rT) (f : aT -> rT).

Lemma injective_left_inverse A f :
  {in A &, injective f} -> {in A, cancel f (inverse t0 A f)}.
 Proof.
move=> fi a; rewrite in_setE => Aa; rewrite /inverse.
case: xgetP => [t ? [] ffat At|/(_ a) []//].
by move/fi : ffat; apply => //; rewrite in_setE.
Qed.

Lemma injective_right_inverse A B f : {in A &, injective f} ->
  B `<=` f @` A -> {in B, cancel (inverse t0 A f) f}.
Proof.
move=> fi BfA b; rewrite in_setE => Bb; rewrite /inverse.
by case: xgetP => [t ? []//|]; case/(_ _ Bb) : BfA => t ? ? /(_ t) [].
Qed.

Lemma surjective_right_inverse A B f : surjective A B f ->
  {in B, cancel (inverse t0 A f) f}.
Proof.
move=> fsur a; rewrite in_setE => Aa; rewrite /inverse; case: xgetP.
  by move=> u ->{u} []; rewrite /preimage /set1 => ->.
by have [u [Au afu]]:= fsur _ Aa; move/(_ u) => [].
Qed.

End inverse_lemmas.

Notation "'`I_' n" := [set k | (k < n)%N].

Lemma II0 : `I_0 = set0. Proof. by rewrite predeqE. Qed.

Lemma II1 : `I_1 = [set 0%N].
Proof. by rewrite predeqE; case. Qed.

Lemma IIn_eq0 n : `I_n = set0 -> n = 0%N.
Proof. by case: n => // n; rewrite predeqE; case/(_ 0%N); case. Qed.

Lemma II_recr n : `I_n.+1 = `I_n `|` [set n].
Proof.
rewrite /mkset predeqE => i; split => [|[|->//]].
by rewrite ltnS leq_eqVlt => /orP[/eqP ->|]; by [left|right].
by move/ltn_trans; apply.
Qed.

Lemma set_bijective_D1 T n (A : set T) (f : nat -> T) :
  set_bijective `I_n.+1 A f -> set_bijective `I_n (A `\ f n) f.
Proof.
move=> bij_f; split.
- move=> i j; rewrite 2!in_setE => ni nj.
  move/(inj_of_bij bij_f); rewrite 2!in_setE.
  by move=> /(_ (ltn_trans ni (ltnSn _))) /(_ (ltn_trans nj (ltnSn _))).
- move=> t [i ni fit].
  have : (f @` `I_n.+1) t by exists i => //; rewrite /mkset (ltn_trans ni).
  move/(sub_of_bij bij_f) => At; split => //.
  rewrite /set1 -fit => /(inj_of_bij bij_f).
  rewrite 2!in_setE => /(_ (ltn_trans ni (ltnSn _))) /(_ (ltnSn _)) => niE.
  by move: ni; rewrite /mkset niE ltnn.
- move=> t [At]; rewrite /set1 => tfn.
  have [i [ni1 tfi]] := (sur_of_bij bij_f) _ At.
  exists i; split => //; move: ni1; rewrite /mkset leq_eqVlt => /orP[/eqP[niE]|].
    by move: tfi; rewrite niE.
  by rewrite ltnS.
Qed.

Lemma pigeonhole m n (f : nat -> nat) : {in `I_m &, injective f} ->
  f @` `I_m `<=` `I_n -> (m <= n)%N.
Proof.
elim: n m f => [n f fi|n ih m f fi fmn1].
  by rewrite II0 subset0 => /image_set0_set0 /IIn_eq0 => ->.
have : (forall i, i < m -> f i < n)%N \/ (exists i, i < m /\ n = f i)%N.
  have [|/existsNP] := pselect (forall i, i < m -> f i < n)%N; first by left.
  move=> [x] /not_implyP[xm /negP fxn]; right; exists x; split => //.
  by apply/eqP; rewrite eqn_leq leqNgt fxn /= -ltnS fmn1 //; exists x.
move=> [mn|[i0 [i0m fi0]]].
  have fmn : f @` `I_ m `<=` `I_n by move=> i [j] jm <-{i}; exact: mn.
  by move/ih : fi => /(_ fmn); move/leq_trans; apply.
pose g i := if (i < i0)%N then i else i.+1.
have inj_g : {in `I_m.-1 &, injective g}.
  move=> i j; rewrite !in_setE /g => mi mj; have [ii0|ii0] := ltnP i i0.
    by have [//|/(leq_trans ii0) /ltnW + ij] := ltnP j i0; rewrite ij ltnn.
  by have [/leq_trans/(_ ii0)/ltnW + ij|_ []//] := ltnP j i0; rewrite -ij ltnn.
have gm1m : g @` `I_m.-1 `<=` `I_m.
  move=> i [j] jm1 <-{i}; rewrite /g.
  by have [/ltn_trans|_] := ltnP j i0; [exact|rewrite /mkset -ltn_predRL].
have f1m1n : (f \o g) @` `I_m.-1 `<=` `I_n.
  move=> _ [y] ym <-; rewrite /= /g; have [yi0|i0y]:= ltnP y i0.
  - have : (f y < n.+1)%N.
      move: fmn1; rewrite /mkset; apply.
      by exists y; rewrite // (leq_trans _ (leq_pred _)).
    rewrite ltnS leq_eqVlt => /orP[|//]; rewrite fi0 => /eqP /fi.
    rewrite /mkset => yi0E.
    by move: yi0; rewrite yi0E ?ltnn// in_setE // (leq_trans ym) // leq_pred.
  - have : (f y.+1 < n.+1)%N.
      by move: fmn1; rewrite /mkset; apply; exists y.+1; rewrite // -ltn_predRL.
    rewrite ltnS leq_eqVlt => /orP[|//]; rewrite fi0 => /eqP /fi.
    rewrite /mkset => yi0; move: i0y.
    by rewrite -yi0 ?ltnn// in_setE// -ltn_predRL.
have /ih : {in `I_m.-1 &, injective (f \o g)}.
  apply: (in_inj_comp fi inj_g) => x; rewrite !in_setE /g => xm1.
  by have [/ltn_trans|] := ltnP x i0; [exact|rewrite /mkset -ltn_predRL].
by move/(_ f1m1n); rewrite -subn1 leq_subLR add1n.
Qed.

Theorem Cantor_Bernstein T (U : pointedType) (A : set T) (B : set U)
  (f : T -> U) (g : U -> T) :
  {in A &, injective f} -> f @` A `<=` B ->
  {in B &, injective g} -> g @` B `<=` A ->
  exists f0 : T -> U, set_bijective A B f0.
Proof.
move=> fi fAB gi gBA.
pose A_ := fix h n := if n is m.+1 then g @` (f @` (h m)) else A `\` (g @` B).
have A_A : forall k t, A_ k t -> A t.
  elim => [t []//|n ih t /= [u [t']] /ih At <- <-].
  by apply gBA; exists (f t') => //; apply fAB; exists t'.
pose X := \bigcup_i (A_ i).
pose Y := A `\` X.
have Ygb : Y `<=` g @` B.
  have -> : Y = (g @` B) `&` (A `\` \bigcup_i (A_ i.+1)).
    rewrite /Y [X in _ `\` X](_ : _ = A_ 0%N `|` \bigcup_i (A_ i.+1)); last first.
      by rewrite /X (bigcup_splitn 1) big_ord_recl big_ord0 setU0.
    by rewrite setDUr [A_ 0%N]/= setDD; move/setIidPl : gBA; rewrite setIC => ->.
  by apply subIset; left.
exists (fun t => if pselect (X t) is left _ then f t else (inverse point B g) t).
split => [a b | u [t At <-{u}] | b Bb].
- rewrite 2!in_setE => Aa Ab; case: pselect => Xa.
    case: pselect => [Xb|Xb /(congr1 g) ab]; first by apply fi; rewrite in_setE.
    suff : X (g (f a)).
      by rewrite ab (injective_right_inverse point _ Ygb) // in_setE.
    have [i Aia] : exists i, (A_ i) a by case: Xa => i _ ?; exists i.
    by exists i.+1 => //=; exists (f a) => //; exists a.
  case: pselect => [Xb /(congr1 g) ab|Xb /(congr1 g)]; last first.
    by do 2 rewrite (injective_right_inverse point _ Ygb) ?in_setE//.
  suff : X (g (f b)).
    by rewrite -ab (injective_right_inverse point _ Ygb) ?in_setE.
  have [i Aib] : exists i, (A_ i) b by case: Xb => i _ ?; exists i.
  by exists i.+1 => //=; exists (f b) => //; exists b.
- case: pselect => [[i _ Ait]|Xt]; first by apply fAB; exists t.
  have [u Bu <-] : (g @` B) t.
    have {}Xt : forall i, (~` A_ i) t by move=> i ?; apply Xt; exists i.
    by have /= := Xt 0%N; rewrite /A_ setDE setCI setCK => -[|].
  by rewrite injective_left_inverse // in_setE.
- have [Xgb|Xgb] := pselect (X (g b)); last first.
    exists (g b); split; first by apply gBA; exists b.
    by case: pselect => // _; rewrite injective_left_inverse // in_setE.
  have A0gb : ~ (A_ 0%N) (g b) by move=> [Agb]; apply; exists b.
  have [i Aigb] : exists i, (A_ i) (g b) by case: Xgb => i _ ?; exists i.
  case: i Aigb A0gb => [//|i] Aigb A0gb.
  have [c [Aic gbgfc]] : exists c, (A_ i) c /\ g b = g (f c).
    by move: Aigb => /= [u [t ? <-{u} ?]]; exists t.
  exists c; split; first by apply: A_A Aic.
  case: pselect => [Xc|Xc].
    move/gi : (gbgfc); apply => //; rewrite in_setE //.
    by apply fAB; exists c => //; exact: A_A Aic.
  by exfalso; apply Xc; exists i.
Qed.

Definition card_le T U (A : set T) (B : set U) := exists f : T -> U,
  {in A &, injective f} /\ f @` A `<=` B.

Notation "A '#<=' B" := (card_le A B).

Lemma card_le_surj (T : pointedType) U (A : set T) (B : set U) :
  A #<= B -> exists g : U -> T, surjective B A g.
Proof.
move=> -[f [finj fAB]]; exists (inverse point A f).
move=> t At; exists (f t); split; first by apply fAB; exists t.
by rewrite injective_left_inverse // in_setE.
Qed.

Lemma surj_card_le T (U : pointedType) (A : set T) (B : set U) (g : U -> T) :
  A !=set0 -> surjective B A g -> A #<= B.
Proof.
move=> A0 gsurj; exists (inverse point B g); split => [a b|u [t At] <-].
  rewrite 2!in_setE => Aa Ab /(congr1 g).
  by do 2 rewrite (surjective_right_inverse point gsurj) ?in_setE//.
rewrite /inverse; case: xgetP => [v Hv []//|] /=.
by have [w [Bw agw] /(_ w) []] := gsurj _ At.
Qed.

Lemma card_lexx T (A : set T) : A #<= A.
Proof. by exists id; split => // t [] t0 At0 <-. Qed.

Lemma card_le0x T (U : pointedType) (S : set U) : @set0 T #<= S.
Proof. by exists (fun=> point); split => [| ? []//] => x y; rewrite in_setE. Qed.

Lemma card_le_trans (T U : Type) V (B : set U) (A : set T) (C : set V) :
  A #<= B -> B #<= C -> A #<= C.
Proof.
move=> [f [fi fAB]] [g [gi gBC]]; exists (g \o f); split.
  apply: (in_inj_comp gi fi) => t; rewrite 2!in_setE => At.
  by apply fAB; exists t.
move=> v [t At] <-{v}.
by apply gBC; exists (f t) => //; apply fAB; exists t.
Qed.

Lemma card_le0P T (U : pointedType) (A : set T) : A #<= @set0 U <-> A = set0.
Proof.
split; last by move=> ->; apply: card_le0x.
case=> f [fi]; rewrite subset0 => fA0; rewrite predeqE => t; split => // At.
by move: fA0; rewrite predeqE => /(_ (f t)) => -[fA0 _]; apply: fA0; exists t.
Qed.

Lemma card_le_II n m : (n <= m)%N <-> `I_n #<= `I_m.
Proof.
split=> [nm|[f [gi]]]; last exact: pigeonhole.
by exists id; split => //; rewrite image_id => t; move/leq_trans; apply.
Qed.

Definition card_eq T U (A : set T) (B : set U) := A #<= B /\ B #<= A.

Notation "A '#=' B" := (card_eq A B) (at level 79, format "A  '#='  B").

Lemma card_eq_sym T U (A : set T) (B : set U) : A #= B -> B #= A.
Proof. by rewrite /card_eq => -[]. Qed.

Lemma card_eq_trans T U V (A : set T) (B : set U) (C : set V) :
  A #= B -> B #= C -> A #= C.
Proof.
move=> [AB BA] [BC CB]; split;
  by [apply (card_le_trans AB) | apply (card_le_trans CB)].
Qed.

Lemma card_eq0 T (U : pointedType) (A : set T) : A #= @set0 U -> A = set0.
Proof. by case => /card_le0P. Qed.

Lemma card_eq00 (T U : pointedType) : @set0 T #= @set0 U.
Proof. by split; apply/card_le0x. Qed.

Lemma card_eqP (T : pointedType) (U : pointedType) (A : set T) (B : set U) :
  A #= B <-> exists f : T -> U, set_bijective A B f.
Proof.
split=> [[[f [finj fAB] [g [ginj fBA]]]]|[f [fi fAB fs]]].
  exact: (Cantor_Bernstein finj fAB ginj).
split; first by exists f.
have [->|/set0P B0] := eqVneq B set0; first by exact: card_le0x.
exact: (@surj_card_le _ _ _ _ f).
Qed.

Lemma card_eqTT (T : pointedType) : @setT T #= @setT T.
Proof. by apply/card_eqP; exists id; split => // x _; exists x. Qed.

Lemma card_eq_II n m : n = m <-> `I_n #= `I_m.
Proof.
split => [/eqP|[nm mn]].
  rewrite eqn_leq => /andP[nm mn].
  by split; [apply/card_le_II|apply/card_le_II].
by apply/eqP; rewrite eqn_leq; apply/andP; split; apply/card_le_II.
Qed.

Lemma card_eq_le T U V (A : set T) (B : set U) (C : set V) :
  A #= B -> C #<= A -> C #<= B.
Proof. by case => AB _; move/card_le_trans; apply. Qed.

Lemma card_eq_ge T U V (A : set T) (B : set U) (C : set V) :
  A #= C -> A #<= B -> C #<= B.
Proof. by case => _ CA; apply/card_le_trans. Qed.

Lemma card_leP (T U : pointedType) (A : set T) (B : set U) :
  A #<= B <-> exists C, C `<=` B /\ A #= C.
Proof.
split=> [[f [fi fAB]]|[C [CB /card_eq_sym AC]]]; last first.
 by apply: (card_eq_ge AC); exists id; split => //; rewrite image_id.
have AfAf := set_bijective_image fi.
by exists (f @` A); split => //; apply/card_eqP; exists f.
Qed.

Lemma set_bijective_inverse
    (T U : pointedType) (A : set T) (B : set U) (f : T -> U) :
  set_bijective A B f -> exists g, set_bijective B A g.
Proof. by move=> ABf; apply/card_eqP/card_eq_sym/card_eqP; exists f. Qed.

Definition countable T (A : set T) := A #<= @setT nat.

Lemma countable0 T : countable (@set0 T).
Proof. by exists (fun=> 0%N); split => // x y; rewrite in_setE. Qed.

Lemma countable_injective T (A : set T) :
  countable A <-> exists f : T -> nat, {in A &, injective f}.
Proof. by split; [case=> f [? _]; exists f | move=> [f fi]; exists f]. Qed.

Lemma countable_trans T U (A : set T) (B : set U) (f : T -> U) : countable B ->
  {in A &, injective f} -> f @` A `<=` B -> countable A.
Proof.
rewrite /countable => -[g [ginj gBnat]] fA fAB; exists (g \o f); split => //.
move=> x y; rewrite 2!in_setE => xA yA /ginj => xy.
apply/fA; rewrite ?in_setE//; apply xy; by [
  rewrite in_setE; apply fAB; exists x | rewrite in_setE; apply fAB; exists y].
Qed.

Definition set_finite (T : choiceType) (A : set T) :=
  exists A' : {fset T}, A = [set x | x \in A'].

Lemma set_finiteP (T : pointedType) (A : set T) :
  set_finite A <-> exists n, A #= `I_n.
Proof.
split=> [[A' AA']|].
- exists #|`A'|; apply/card_eqP; exists (index^~ A'); split.
  + move=> t0 t1; rewrite AA' /mkset 2!in_setE => t0A' t1A'.
    by move/(congr1 (nth t0 A')); rewrite nth_index // nth_index.
  + by move=> /= i [t]; rewrite AA' /mkset -index_mem => tA' <-.
  + move=> /= i ?; exists (nth point A' i); rewrite AA' /mkset mem_nth //.
    by rewrite index_uniq.
- move=> -[n] /card_eqP[/= f] /set_bijective_inverse[f1 bij_f1].
  exists [fset x | x in map f1 (iota 0 n)]%fset; rewrite predeqE => t; split.
    move=> At; rewrite /mkset inE /=; apply/mapP.
    have [/= i [ni ->]] := (sur_of_bij bij_f1) _ At.
    by exists i => //; rewrite mem_iota add0n.
  rewrite /mkset inE /= => /mapP[i]; rewrite mem_iota add0n leq0n /= => ni ->{t}.
  by apply: (sub_of_bij bij_f1); exists i.
Qed.

Lemma set_finite_seq (T : choiceType) (s : seq T) :
  set_finite [set i | i \in s].
Proof.
by exists [fset x in s]%fset; rewrite predeqE => t; split; rewrite /mkset inE.
Qed.

Lemma set_finite_countable (T : pointedType) (A : set T) :
  set_finite A -> countable A.
Proof.
by move=> /set_finiteP[n /card_eqP[f Anf]]; exists f; split => //;
  exact: (inj_of_bij Anf).
Qed.

Lemma set_finite0 (T : pointedType) : set_finite (@set0 T).
Proof. by exists fset0; rewrite predeqE. Qed.

Section set_finite_bijection.

Local Lemma set_bijective_U1 (T : pointedType) n (f g : nat -> T) (A : set T) :
  set_bijective `I_n.+1 A f ->
  set_bijective `I_n (A `\ f n) g ->
  set_bijective `I_n.+1 A (fun m => if (m < n)%N then g m
                                 else if m == n then f n
                                 else point).
Proof.
move=> bij_f bij_g; split => [i j|t [i]|t At].
- rewrite /mkset in_setE leq_eqVlt => /orP[/eqP[->{i}]|].
    rewrite ltnn eqxx in_setE leq_eqVlt => /orP[/eqP[->{j}]|].
      by rewrite ltnn eqxx; apply (inj_of_bij bij_f) => //; rewrite in_setE /mkset ltnS.
    rewrite ltnS => jn; rewrite jn => fngj.
    suff : (A `\ f n) (f n) by case => _; rewrite /set1 /mkset.
    by apply (sub_of_bij bij_g); exists j => // -[].
  rewrite ltnS => ni; rewrite in_setE leq_eqVlt => /orP[/eqP[ ->{j}]|].
    rewrite ni ltnn eqxx => gifn.
    suff : (A `\ f n) (f n) by case => _; rewrite /set1 /mkset.
    by apply (sub_of_bij bij_g); exists i.
  rewrite ltnS => jn; rewrite ni jn.
  by apply (inj_of_bij bij_g); rewrite in_setE.
- rewrite /mkset leq_eqVlt => /orP[/eqP[->{i}]|].
    rewrite ltnn eqxx => <-{t}.
    by apply (sub_of_bij bij_f); exists n => //; rewrite /mkset ltnSn.
  by rewrite ltnS => ni1 <-{t}; rewrite ni1; apply (sub_of_bij bij_g); exists i.
- have [/= i []] := (sur_of_bij bij_f) _ At.
  rewrite leq_eqVlt => /orP[/eqP[->{i} ->]|].
    by exists n; split => //; rewrite ltnn eqxx.
  rewrite ltnS => ni tfi; rewrite tfi.
  have Afnt : (A `\ f n) t.
    rewrite /set1; split => // tfn.
    suff niE : i = n by move: ni; rewrite niE ltnn.
    move: tfn; rewrite tfi; move/(inj_of_bij bij_f).
    by rewrite /mkset !in_setE; apply => //; rewrite (ltn_trans ni).
  have [j [jn tgj]] := (sur_of_bij bij_g) _ Afnt.
  by exists j; split; [rewrite (ltn_trans jn) | rewrite jn -tgj].
Qed.

Local Lemma set_bijective_cyclic_shift (T : pointedType) n (f g : nat -> T)
    (A : set T) :
  set_bijective `I_n.+1 A f ->
  set_bijective `I_n (A `\ f n) g ->
  set_bijective `I_n.+1 A (fun m => if m == 0%N then f n
                                 else if (m < n.+1)%N then g m.-1
                                 else point).
Proof.
move=> bij_f bij_g; split=> [i j|t [i in2]|t At].
- rewrite 2!in_setE => in1 jn1.
  have [/eqP i0|i0] := ifPn _.
    have [/eqP j0|j0] := ifPn _; first by rewrite i0 j0.
    rewrite jn1 => fngj1.
    suff : (A `\ f n) (f n) by move=> -[]; rewrite /set1 /mkset.
    apply (sub_of_bij bij_g); rewrite fngj1; exists j.-1 => //.
    by rewrite /mkset prednK ?lt0n.
  rewrite in1.
  have [/eqP j0 gi1fn|j0] := ifPn _.
    suff : (A `\ f n) (f n) by move=> -[]; rewrite /set1 /mkset.
    apply (sub_of_bij bij_g); rewrite -gi1fn; exists i.-1 => //.
    by rewrite /mkset prednK ?lt0n.
  rewrite jn1 => /(inj_of_bij bij_g).
  rewrite 2!in_setE /mkset prednK ?lt0n// -ltnS in1 prednK ?lt0n// -ltnS jn1.
  by move/(_ isT isT) => /(congr1 S); rewrite !prednK ?lt0n.
- have [/eqP i0 <-{t}|i0] := ifPn _.
    by apply (sub_of_bij bij_f); rewrite /mkset; exists n.
  rewrite in2 => <-{t}.
  by apply (sub_of_bij bij_g); exists i.-1 => //; rewrite /mkset prednK ?lt0n.
- have [i []] := (sur_of_bij bij_f) _ At.
  rewrite /mkset leq_eqVlt => /orP[/eqP [->{i} tgn1]|]; first by exists 0%N.
  rewrite ltnS => ni tfi.
  have : (A `\ f n) (f i).
    split.
      apply: (sub_of_bij bij_f); exists i => //.
      by rewrite /mkset (ltn_trans ni).
    rewrite /set1 => /(inj_of_bij bij_f); rewrite 2!in_setE.
    move/(_ (ltn_trans ni _)) => /(_ (ltnSn _)) /(_ (ltnSn _)) => niE.
    by move: ni; rewrite niE ltnn.
  move/(sur_of_bij bij_g) => [j [jn figj]].
  by exists j.+1; split; [rewrite ltnS|rewrite /= ltnS jn tfi].
Qed.

Local Lemma set_bijective_cyclic_shift_simple (T : pointedType) n (f : nat -> T)
    (A : set T) :
  set_bijective `I_n.+1 A f ->
  set_bijective `I_n.+1 A (fun m => if m is 0 then f n else f m.-1).
Proof.
move=> bij_f.
have := set_bijective_cyclic_shift bij_f (set_bijective_D1 bij_f).
apply: set_bijective1 => i; rewrite in_setE => ni1.
by case: ifPn => [/eqP -> //|i0]; rewrite ni1; case: i ni1 i0.
Qed.

Lemma set_finite_bijective (T : pointedType) (A : set T) n S : A !=set0 ->
  A #= `I_n -> S `<=` A ->
  exists f, set_bijective `I_n A f /\
    exists k, (k <= n)%N /\ (f @^-1` S) `&` `I_n = `I_k.
Proof.
case: n S => [S /set0P A0 Ac0 _|n S].
  suff : A #= @set0 T by move/card_eq0/eqP; rewrite (negbTE A0).
  move/card_eq_trans : Ac0; apply.
  by rewrite II0; exact: card_eq00.
move: n A S; elim=> [A S [t At] A1 SA|n ih A S A0 /card_eq_sym].
  have {}At : A = [set t].
    rewrite predeqE => t'; split=> [At'|->//].
    apply/eqP/negPn/negP => t't.
    have A2 : `I_2 #<= A.
      exists (fun n => if n is 0 then t else t'); split.
      - move=> x y; rewrite 2!in_setE.
        move: x y => [|[|//]] [|[|//]] // _ _ /eqP.
        by rewrite eq_sym (negbTE t't).
        by rewrite (negbTE t't).
      - by move=> ? [] [|[|//]] _ <-.
    by move/card_le_II : (card_eq_le A1 A2); rewrite ltnn.
  move: A1 SA; rewrite {}At {A}.
  exists (fun=> t); split; first split.
    - by move=> x y; rewrite !in_setE; move: x y => [|//] [|//].
    - by move=> x [i _] <-.
    - by move=> u ->; exists 0%N.
  have [S0|S1] := subset_set1 SA.
  - by exists 0%N; split => //; rewrite predeqE => i; rewrite S0 /= set0I.
  - by exists 1%N; split => //; rewrite predeqE S1 => i; split => //= -[].
move => /card_eqP [g bij_g] SA.
have [S0|] := pselect (S !=set0); last first.
  move/set0P/negP; rewrite negbK => /eqP ->.
  exists g; split => //; exists 0%N; split => //.
  by rewrite preimage_set0 set0I II0.
have bij_h : set_bijective `I_n.+1 (A `\ g n.+1) _ := set_bijective_D1 bij_g.
pose A' := A `\ g n.+1.
have A'n : A' #= `I_n.+1 by exact/card_eqP/(set_bijective_inverse bij_h).
pose S' := S `\ g n.+1.
have [Sgn1|Sgn1] := pselect (S (g n.+1)); last first.
  have SA' : S `<=` A'.
    rewrite (_ : S = S `\ g n.+1); first exact: setSD.
    rewrite predeqE => t; split => [St|]; last by case.
    by split => // tgn2; apply Sgn1; rewrite -tgn2.
  have A'0 := subset_nonempty SA' S0.
  have [h' [bij_h' [k [kn h'S]]]] := ih _ _ A'0 A'n SA'.
  have bij_f : set_bijective `I_n.+2 A _ := set_bijective_U1 bij_g bij_h'.
  set f := (X in set_bijective _ _ X) in bij_f.
  have fh' : (f @^-1` S) `&` `I_n.+1 = (h' @^-1` S) `&` `I_n.+1.
    rewrite predeqE => i; split => [[fSi in1]|[h'Si in1]].
      by split => //; move: fSi; rewrite /preimage /mkset /f in1.
    by split => //; rewrite /preimage /mkset /f in1.
  have h'k : (h' @^-1` S) `&` `I_n.+1 = `I_k by [].
  exists f; split => //.
  exists k; split; first by rewrite (leq_trans kn).
  rewrite -h'k -fh' predeqE => j; split => [[fSj]|[fjS jn1]].
    rewrite /mkset leq_eqVlt => /orP[/eqP[jn1]|]; split=> //.
    by move: fSj; rewrite /preimage /mkset /f jn1 ltnn eqxx.
  by split => //; rewrite /mkset (ltn_trans jn1).
have S'A' : S' `<=` A' by apply setSD.
have [S'0|] := pselect (S' !=set0); last first.
  move/set0P/negP; rewrite negbK => /eqP S'0.
  have -> : S = [set g n.+1].
    move: S'0; rewrite setD_eq0.
    by move/(@subset_set1 _ S) => [/eqP/negPn/negP/set0P //|].
  eexists; split; first exact: (set_bijective_cyclic_shift_simple bij_g).
  exists 1%N; split => //.
  rewrite predeqE => -[//|i /=]; split=> // -[] /=; rewrite /set1 => gign1.
  rewrite ltnS => in1.
  move/(inj_of_bij bij_g) : gign1; rewrite !in_setE.
  move/(_ (leq_trans in1 (leqnSn _)) (ltnSn _)) => ni1.
  by move: in1; rewrite ni1 ltnn.
have A'0 := subset_nonempty S'A' S'0.
have [h' [bij_h' [k [kn h'S]]]] := ih _ _ A'0 A'n S'A'.
have bij_f : set_bijective `I_n.+2 A _ := set_bijective_cyclic_shift bij_g bij_h'.
set f := (X in set_bijective _ _ X) in bij_f.
have fh' : (f @^-1` S) `&` `I_n.+2 =
    ([set 0%N] `|` [set m | (h' @^-1` S') m.-1]) `&` `I_n.+2.
  rewrite predeqE => i; split.
    move=> [fSi in1]; split => //.
    have [->|i0] := eqVneq i 0%N; [by left | right].
    move: fSi; rewrite /preimage /mkset /f (negbTE i0) in1 // => Sh'i1.
    split => //; rewrite /set1 => h'i1gn1.
    suff  : A' (g n.+1) by case; rewrite /set1 /mkset.
    rewrite -h'i1gn1; apply (sub_of_bij bij_h'); exists i.-1 => //.
    by rewrite /mkset prednK ?lt0n // ltnW.
  move=> [[|]]; first by rewrite /set1 => ->{i} _.
  rewrite /preimage => -[Sh'i1]; rewrite /set1 => h'i1gn1 in1.
  by split => //; rewrite /f /mkset; case: ifPn => i0 //; rewrite in1.
have h'k : ([set 0%N] `|` [set m | (h' @^-1` S') m.-1]) `&` `I_n.+2 = `I_k.+1.
  rewrite predeqE => i; split => [[]|].
    case; first by rewrite /set1 => ->.
    have [->//|i0] := eqVneq i 0%N.
    rewrite /preimage => S'h'i1 in2.
    move: h'S; rewrite predeqE.
    move/(_ i.-1) => [H _].
    have /H : (h' @^-1` S' `&` (fun k => (k < n.+1)%N)) i.-1.
      by split => //; rewrite -ltnS (leq_trans _ in2) // ltnS prednK // lt0n.
    by rewrite /mkset ltnS; apply leq_trans; rewrite prednK // lt0n.
  have [k0|k0] := eqVneq k 0%N.
    by rewrite /mkset k0 ltnS leqn0 => /eqP ->; split => //; left.
  rewrite /mkset ltnS leq_eqVlt => /orP[/eqP ->{i}|ik].
    split => //; right; move: h'S; rewrite predeqE => /(_ k.-1) [_].
    by rewrite /mkset ltn_predL lt0n => /(_ k0) [].
  have [->|i0] := eqVneq i 0%N; first by split => //; left.
  split; last by rewrite (ltn_trans ik).
  right; rewrite /preimage; move: h'S.
  rewrite predeqE.
  move/(_ i.-1) => [_] H.
  suff : (i.-1 < k)%N by move/H; case.
  by rewrite (leq_trans _ ik) // ltnS leq_pred.
by exists f; split => //; exists k.+1; split => //; rewrite -h'k fh'.
Qed.

End set_finite_bijection.

Local Corollary subset_set_finite_card_le (T : pointedType) (A B : set T) :
  A `<=` B -> set_finite B -> set_finite A /\ A #<= B.
Proof.
move=> AB /set_finiteP[n Bn].
have [B0|/set0P B0] := eqVneq B set0.
  move: AB; rewrite B0 subset0 => ->.
  by split; [exact: set_finite0|exact: card_le0x].
have [f [bij_f [k [kn fAk]]]] := set_finite_bijective B0 Bn AB.
have := set_bijective_subset bij_f AB.
rewrite fAk => bij_f1; split.
  by apply/set_finiteP; exists k; exact/card_eqP/set_bijective_inverse/bij_f1.
apply: (@card_eq_le _ _ _ `I_n); first exact: card_eq_sym.
apply: (@card_eq_ge _ _ _ `I_k); first by apply/card_eqP; exists f.
exact/card_le_II.
Qed.

Lemma subset_set_finite (T : pointedType) (A B : set T) : A `<=` B ->
  set_finite B -> set_finite A.
Proof. by move=> AB fB; have [] := subset_set_finite_card_le AB fB. Qed.

Lemma subset_card_le (T : pointedType) (A B : set T) : A `<=` B ->
  set_finite B -> A #<= B.
Proof. by move=> AB fB; have [] := subset_set_finite_card_le AB fB. Qed.

Local Corollary injective_set_finite_card_le
  (T U : pointedType) (A : set T) (B : set U) (f : T -> U) :
  {in A &, injective f} -> f @` A `<=` B -> set_finite B ->
  set_finite A /\ A #<= B.
Proof.
move=> inj_f fAB /set_finiteP[n Bn].
have [B0|/set0P/negP/negPn/eqP B0] := pselect (B !=set0); last first.
  move: fAB; rewrite B0 subset0 => /image_set0_set0 ->.
  by split; [exact: set_finite0|exact: card_le0x].
case: (@set_finite_bijective U B n (f @` A) B0 Bn fAB) => h [bij_h [k [kn gfA]]].
have finfA : set_finite (f @` A).
  by apply: (subset_set_finite fAB _); apply/set_finiteP; exists n.
have AfAf := set_bijective_image inj_f.
have finA : set_finite A.
  move/set_finiteP in finfA.
  case: finfA => m /card_eq_sym mfA; apply/set_finiteP; exists m.
  by apply/card_eq_sym/(card_eq_trans mfA)/card_eq_sym/card_eqP; by exists f.
have AfA : A #= f @` A by apply/card_eqP; exists f.
by split => //; exists f.
Qed.

Lemma injective_set_finite (T U : pointedType) (A : set T) (B : set U)
  (f : T -> U) : {in A &, injective f} ->
  f @` A `<=` B -> set_finite B -> set_finite A.
Proof.
by move=> fi AB fB; have [] := injective_set_finite_card_le fi AB fB.
Qed.

Lemma injective_card_le (T U : pointedType) (A : set T) (B : set U)
  (f : T -> U) : {in A &, injective f} ->
  f @` A `<=` B -> set_finite B -> A #<= B.
Proof.
by move=> fi AB fB; have [] := injective_set_finite_card_le fi AB fB.
Qed.

Corollary set_finite_preimage (T U : pointedType) (B : set U) (f : T -> U) :
  {in (f @^-1` B) &, injective f} -> set_finite B -> set_finite (f @^-1` B).
Proof.
by move=> fi; exact: (injective_set_finite fi (@image_preimage_subset _ _ _ _)).
Qed.

Local Corollary surjective_set_finite_card_le
  (T : pointedType) (U : pointedType) (A : set T) (B : set U) (f : T -> U) :
  surjective A B f -> set_finite A ->
  set_finite B /\ B #<= A.
Proof.
have [[a0 Aa0]|/set0P/negP/negPn/eqP ->{A}] := pselect (A !=set0); last first.
  move/surjective_set0 => ->{B} _.
  by split; [exact: set_finite0|exact: card_le0x].
move=> fs finA.
pose a : U -> T := inverse a0 A f.
pose S := (a @` B) `&` A.
have SA : S `<=` A by apply subIset; right.
have [finS {}SA] := subset_set_finite_card_le SA finA.
suff SBf : set_bijective S B f.
  have SB : S #= B by apply/card_eqP; exists f.
  split; last exact: (@card_eq_ge _ _ _ S).
  move/set_finiteP: finS => [n Sn]; apply/set_finiteP; exists n.
  by apply: card_eq_trans Sn; exact/card_eq_sym.
split.
- move=> x y; rewrite 2!in_setE /S => [] [] [u Bu <-{x}] Aau [] [v Bv <-{y} Aav].
  rewrite (surjective_right_inverse a0 fs) ?in_setE//.
  by rewrite (surjective_right_inverse a0 fs) ?in_setE// => ->.
- move=> u [t St <-{u}].
  move: St; rewrite /S => -[] [u Bu <-{t}] Aau.
  by rewrite /a (surjective_right_inverse a0 fs) ?in_setE.
- move=> b Bb; exists (a b); split.
    rewrite /S; split; first by exists b.
    rewrite /a /inverse; case: xgetP=> [? ? []|] //.
  by rewrite (surjective_right_inverse a0 fs) // ?in_setE.
Qed.

Lemma surjective_set_finite
  (T : pointedType) (U : pointedType) (A : set T) (B : set U) (f : T -> U) :
  surjective A B f -> set_finite A -> set_finite B.
Proof. by move=> ABf fA; have [] := surjective_set_finite_card_le ABf fA. Qed.

Lemma surjective_card_le
  (T : pointedType) (U : pointedType) (A : set T) (B : set U) (f : T -> U) :
  surjective A B f -> set_finite A -> B #<= A.
Proof. by move=> ABf fA; have [] := surjective_set_finite_card_le ABf fA. Qed.

Lemma set_finite_diff (T : pointedType) (A B : set T) : set_finite A ->
  set_finite (A `\` B).
Proof.
move=> fA.
by have [] := (@subset_set_finite_card_le _ (A `\` B) A) _ fA => // t [].
Qed.

Lemma card_le_diff (T : pointedType) (A B : set T) : set_finite A ->
  A `\` B #<= A.
move=> fA.
by have [] := (@subset_set_finite_card_le _ (A `\` B) A) _ fA => // t [].
Qed.

Lemma set_finite_inter_set0_union (T : pointedType) (A B : set T) :
  set_finite A -> set_finite B -> A `&` B = set0 -> set_finite (A `|` B).
Proof.
move=> /set_finiteP[n /card_eq_sym/card_eqP[f bij_f]].
move=> /set_finiteP[m /card_eq_sym/card_eqP[g bij_g]] AB.
apply/set_finiteP; exists (n + m)%N; apply/card_eq_sym/card_eqP.
pose h := (fun k => if k < n then f k
          else if k < n + m then g (k - n)
          else point)%N.
exists h; split.
- move=> j k; rewrite 2!in_setE => jnm knm hjhk.
  have /orP[/andP[jn kn]|/andP[/andP[nj jnm'] /andP[nk knm']]] :
      (((j < n) && (k < n)) || ((n <= j < n + m) && (n <= k < n + m)))%N.
  - move: hjhk; rewrite /h jnm knm; have [jn|jn] /= := ltnP j n.
      have Afj : A (f j) by apply (sub_of_bij bij_f); exists j.
      have [//|kn /= fjgkn] := ltnP k n.
      have Bfj : B (f j).
        apply (sub_of_bij bij_g); exists (k - n)%N => //.
        by rewrite /mkset ltn_subLR // leqNgt.
      by move: AB; rewrite predeqE => /(_ (f j)) [] /(_ (conj Afj Bfj)).
    have [kn gjnfk /=|kn //] := ltnP k n.
    have Afk : A (f k) by apply (sub_of_bij bij_f); exists k.
    have Bfk : B (f k).
      apply (sub_of_bij bij_g); rewrite -gjnfk; exists (j - n)%N => //.
      by rewrite /mkset ltn_subLR.
    by move: AB; rewrite predeqE => /(_ (f k)) [] /(_ (conj Afk Bfk)).
  move: hjhk; rewrite /h jn kn.
    by apply (inj_of_bij bij_f); rewrite in_setE.
  move: hjhk; rewrite /h ltnNge nj jnm' /= ltnNge nk knm' /=.
  move/(inj_of_bij bij_g); rewrite /mkset 2!in_setE !ltn_subLR //.
  by move/(_ jnm knm) => /(congr1 (addn^~ n)); rewrite subnK // subnK.
- move=> t [/= i inm]; rewrite /h inm.
  have [ni <-{t}|ni <-{t}] := ltnP i n.
    by left; apply (sub_of_bij bij_f); exists i.
  right; apply (sub_of_bij bij_g); exists (i - n)%N => //.
  by rewrite /mkset ltn_subLR // leqNgt.
- move=> t [At|Bt].
    have [i [ni tfi]] := (sur_of_bij bij_f) _ At.
    by exists i; rewrite /mkset (leq_trans ni) ?leq_addr// /h ni.
  have [i [mi tgi]] := (sur_of_bij bij_g) _ Bt.
  exists (n + i)%N; rewrite /mkset /h ltn_add2l mi ltnNge leq_addr addnC.
  by rewrite addnK.
Qed.

Lemma set_finite_inter (T : pointedType) (A B : set T) :
  (set_finite A \/ set_finite B) -> set_finite (A `&` B).
Proof.
move=> [fA|fB].
- move: (@subIset _ A B A (or_introl (fun=> id))).
  by move/subset_set_finite => /(_ fA).
- move: (@subIset _ A B B (or_intror (fun=> id))).
  by move/subset_set_finite => /(_ fB).
Qed.

Section infinite_subset_enum.
Variable (T : pointedType) (A : set T).
Hypothesis infiniteA : ~ set_finite A.

Lemma ex_in_D : forall s : seq T, exists a, a \in A `\` [set i | i \in s].
Proof.
move=> s; apply/set0P/negP => /eqP As.
have {}As : A `<=` (fun i => i \in s).
  move=> t At; apply/negP=> ts; move: As.
  by rewrite predeqE => /(_ t) -[]; apply: absurd; rewrite in_setE.
exact/infiniteA/(subset_set_finite As _)/set_finite_seq.
Qed.

End infinite_subset_enum.

Section infinite_nat_subset_enum.
Variable A : set nat.
Hypothesis infiniteA : ~ set_finite A .

Definition min_of_D s := ex_minn (ex_in_D infiniteA s).

Definition min_of_D_seq := fix f n :=
  if n is n.+1 then rcons (f n) (min_of_D (f n))
  else [:: min_of_D [::]].

Definition infsub_enum n := last 0%N (min_of_D_seq n).

Lemma min_of_D_seqE n :
  min_of_D_seq n = [seq infsub_enum (nat_of_ord i) | i in 'I_n.+1].
Proof.
elim : n => [|n ih].
  by rewrite /= [RHS](_ : _ = [:: infsub_enum 0%N]) // /image_mem enum_ordS enum0.
rewrite /= [RHS](_ : _ =
    rcons [seq infsub_enum i | i : 'I_n.+1] (infsub_enum n.+1)); last first.
  rewrite {1}/image_mem [in LHS]enum_recr map_rcons /=; congr (rcons _ _).
  by rewrite -map_comp /=; apply eq_map.
by rewrite -ih /infsub_enum /= last_rcons.
Qed.

Lemma increasing_infsub_enum n : (infsub_enum n < infsub_enum n.+1)%N.
Proof.
case : n => [|n]; rewrite /infsub_enum /= 2?last_rcons {2}/min_of_D;
  case: ex_minnP => m; rewrite in_setE => -[Am].
- rewrite /mkset inE => /negP m0 _; rewrite ltn_neqAle eq_sym {}m0 /= /min_of_D.
  by case: ex_minnP => k; rewrite in_setE => _; apply; rewrite in_setE.
- rewrite /mkset mem_rcons inE => /negP; rewrite negb_or => /andP[mn /negP nm] _.
  rewrite ltn_neqAle eq_sym {}mn /= /min_of_D.
  by case: ex_minnP => k; rewrite in_setE => _; apply; rewrite in_setE.
Qed.

Lemma sorted_infsub_enum n :
  sorted ltn [seq infsub_enum (nat_of_ord i) | i in 'I_n.+1].
Proof.
elim : n => [|n]; first by rewrite /image_mem enum_recr map_rcons enum0.
rewrite [in X in X -> _]/image_mem enum_ordS /= -map_comp /= => ih.
rewrite /image_mem enum_ordS /= enum_recr /= -cats1 !map_cat cat_path.
apply/andP; split; first by rewrite -!map_comp in ih *.
rewrite /= andbT /bump leq0n add1n.
case: n {ih} => [|n]; first by rewrite /= enum0 /= increasing_infsub_enum.
rewrite enum_recr /= !map_rcons last_rcons /= /bump leq0n add1n.
by rewrite increasing_infsub_enum.
Qed.

Lemma injective_infsub_enum : injective infsub_enum.
Proof.
move=> x y; apply: contraPP.
suff incr_infsub_enum : {homo infsub_enum : a b / (a < b)%N}.
  move/eqP; rewrite neq_ltn => /orP[xy|yx]; apply/eqP.
    by rewrite ltn_eqF // incr_infsub_enum.
  by rewrite eq_sym ltn_eqF // incr_infsub_enum.
by apply: (homo_ltn ltn_trans) => //; exact: increasing_infsub_enum.
Qed.

Lemma subset_infsub_enum : infsub_enum @` setT `<=` A.
Proof.
move=> n [] m; move: m n; elim=> [n _|m ih n _].
  rewrite /infsub_enum /min_of_D_seq /= /min_of_D /=.
  by case: ex_minnP => // k; rewrite in_setE => -[Ak _ _ <-].
rewrite /infsub_enum /min_of_D_seq /= /min_of_D /= last_rcons /= => <-.
by case: ex_minnP => //= k; rewrite in_setE => -[Ak].
Qed.

Lemma infinite_nat_subset_countable : A !=set0 -> A #= @setT nat.
Proof.
move=> A0.
pose e := infsub_enum; apply/card_eq_sym/card_eqP => /=.
exists e; split; [by move=> x y _ _ /injective_infsub_enum |
  exact: subset_infsub_enum | move=> a Aa].
have : (a <= e a)%N.
  suff : forall n, (n <= e n)%N by [].
  by elim=> // n ih; rewrite (leq_ltn_trans ih) // increasing_infsub_enum.
rewrite leq_eqVlt => /orP[/eqP|] aea; first by exists a.
have amine : (a < min_of_D [seq e (nat_of_ord i) | i in 'I_a.+1])%N.
  have <- : e a.+1 = min_of_D [seq e (nat_of_ord i) | i in 'I_a.+1].
    by rewrite /e /infsub_enum /= last_rcons min_of_D_seqE.
  by rewrite (ltn_trans aea) // increasing_infsub_enum.
have [|/negP aseqf] := boolP (a \in [seq e (nat_of_ord i) | i in 'I_a.+1]).
  by case/mapP => i _ afi; exists i.
suff : (min_of_D [seq e (nat_of_ord i) | i in 'I_a.+1] <= a)%N.
  by rewrite leqNgt amine.
by rewrite /min_of_D; case: ex_minnP => m; rewrite inE => _; apply; rewrite inE.
Qed.

End infinite_nat_subset_enum.

Definition enumeration T (S : set T) (e : nat -> T) := S = e @` setT.

Lemma enumeration_id : enumeration setT id.
Proof. by rewrite /enumeration image_id. Qed.

Lemma enumeration_set0 T (e : nat -> T) : ~ enumeration set0 e.
Proof.
by rewrite /enumeration predeqE => /(_ (e 0%N)) => -[_]; apply; exists 0%N.
Qed.

Section enumeration_wo_repetitions.
Variable (T : pointedType) (A : set T).
Hypothesis infiniteA : ~ set_finite A.
Variables (e : nat -> T) (Ae : enumeration A e).

Lemma ex_enum_notin (s : seq T) : exists m, e m \notin s.
Proof.
apply/not_existsP => Ps.
have {}As : A `<=` (fun i => i \in s).
  by move=> t; rewrite Ae => -[i _ <-]; have /negP/negPn := Ps i.
exact/infiniteA/(subset_set_finite As _)/set_finite_seq.
Qed.

Definition min_of_e s := ex_minn (ex_enum_notin s).

Definition min_of_e_seq := fix h n :=
  if n is n.+1 then rcons (h n) (e (min_of_e (h n)))
  else [:: e 0].

Definition smallest_of_e n := ex_minn (ex_enum_notin (min_of_e_seq n)).

Definition enum_wo_rep n := last point (min_of_e_seq n).

Lemma enum_wo_repE n : enum_wo_rep n.+1 = e (smallest_of_e n).
Proof. by rewrite /enum_wo_rep /min_of_D_seq /= last_rcons. Qed.

Lemma min_of_e_seqE n :
  min_of_e_seq n = [seq enum_wo_rep (nat_of_ord i) | i in 'I_n.+1].
Proof.
elim : n => [|n ih].
  by rewrite [RHS](_ : _ = [:: enum_wo_rep 0%N]) // /image_mem enum_ordS enum0.
rewrite /= [RHS](_ : _ =
    rcons [seq enum_wo_rep i | i : 'I_n.+1] (enum_wo_rep n.+1)); last first.
  rewrite {1}/image_mem [in LHS]enum_recr map_rcons /=; congr (rcons _ _).
  by rewrite -map_comp /=; apply eq_map.
by rewrite -ih /enum_wo_rep /= last_rcons.
Qed.

Lemma smallest_of_e_notin_enum_wo_rep j :
  e (smallest_of_e j) \notin [seq enum_wo_rep (nat_of_ord i) | i in 'I_j.+1].
Proof. by rewrite /smallest_of_e min_of_e_seqE; case: ex_minnP. Qed.

Lemma injective_enum_wo_rep : injective enum_wo_rep.
Proof.
move=> /= i j; apply: contraPP => /eqP.
wlog : i j / (i < j)%N.
  move=> fi.
  rewrite neq_ltn => /orP[ij|ji]; first by apply fi => //; rewrite ltn_eqF.
  by apply/eqP; rewrite eq_sym; apply/eqP/fi => //; rewrite ltn_eqF.
case: j => // j ij1 _.
rewrite [in X in _ <> X]enum_wo_repE.
apply/eqP; apply: contra (smallest_of_e_notin_enum_wo_rep j) => /eqP <-.
by apply/mapP; exists (inord i); rewrite ?inordK // mem_enum inE.
Qed.

Lemma surjective_enum_wo_rep : surjective setT A enum_wo_rep.
Proof.
suff : forall n, (enum_wo_rep @` `I_n.+1) (e n).
   move=> fe t; rewrite Ae => -[i _ tei].
   have [j _ fjei] := fe i.
   by exists j; split => //; rewrite fjei.
apply: ltn_ind => -[_|n ih]; first by exists 0%N.
have [en1f|en1f] :=
    boolP (e n.+1 \in [seq enum_wo_rep (nat_of_ord i) | i in 'I_n.+1]).
  move/mapP : en1f => [/= i _ en1fi].
  by exists i => //; rewrite /mkset (ltn_trans (ltn_ord i)).
have mn1 : smallest_of_e n = n.+1.
  rewrite /smallest_of_e; case: ex_minnP => k /= ekn h.
  apply/eqP; rewrite eqn_leq; apply/andP; split.
    by apply h; rewrite min_of_e_seqE.
  move: ekn; rewrite min_of_e_seqE ltnNge; apply: contra.
  rewrite -ltnS => kn; apply/mapP.
  have [j jk1 gjiek] := ih _ kn.
  exists (inord j).
  by rewrite mem_enum inE.
  by rewrite inordK // (leq_trans jk1).
by rewrite /mkset; exists n.+1 => //; rewrite enum_wo_repE mn1.
Qed.

Lemma set_bijective_enum_wo_rep : set_bijective setT A enum_wo_rep.
Proof.
split; first by move=> i j _ _; apply: injective_enum_wo_rep.
- move=> u [/= i _ <-{u}].
  case: i => [|i]; first by rewrite /enum_wo_rep /= Ae; exists 0%N.
  by rewrite enum_wo_repE /= [X in X (e _)]Ae; exists (smallest_of_e i).
- exact: surjective_enum_wo_rep.
Qed.

End enumeration_wo_repetitions.

(* enum_wo_rep is an enumeration *)
Lemma enumeration_enum_wo_rep (T : pointedType) (A : set T) (e : nat -> T)
  (nfinA : ~ set_finite A) (Ae : enumeration A e) :
  enumeration A (enum_wo_rep nfinA Ae).
Proof.
rewrite /enumeration eqEsubset; split; last first.
  exact: (sub_of_bij (set_bijective_enum_wo_rep nfinA Ae)).
move=> t At; have [x [_ tx]] := (surjective_enum_wo_rep nfinA Ae) _ At.
by exists x.
Qed.

Lemma countable_enumeration (T : pointedType) (A : set T) :
  countable A <-> (A = set0 \/ exists e, enumeration A e).
Proof.
split=> [[f [fi fAT]]|[->|[e Ae]]].
- have [[x Ax]|/set0P/negP/negPn/eqP ->] := pselect (A !=set0); [right|by left].
  pose pi :=
    fun i => if pselect ((f @` A) i) is left _ then inverse x A f i else x.
  exists pi; rewrite /enumeration predeqE => t; split => [At|[i _ <-{t}]].
    exists (f t) => //; rewrite /pi; case: pselect => [_|[]]; last by exists t.
    by rewrite injective_left_inverse ?in_setE.
  rewrite /pi; case: pselect => // -[t At <-{i}].
  by rewrite injective_left_inverse // in_setE.
- exact: card_le0x.
- have [|nfinA] := pselect (set_finite A); first exact: set_finite_countable.
  suff : A #= @setT nat by case.
  apply/card_eq_sym/card_eqP.
  by exists (enum_wo_rep nfinA Ae); exact/set_bijective_enum_wo_rep.
Qed.

Section infinite_nat.

Lemma infinite_nat : ~ set_finite (@setT nat).
Proof.
move=> /set_finiteP[n /card_eq_sym/card_eqP [/= g]].
case: n => [[_ _]|n [_ _ sur_g]].
  by rewrite II0 => /surjective_set0; rewrite predeqE => /(_ 0%N)[] /(_ I).
have [j [jn gj]] := image_nat_maximum n g.
pose m := (g j).+1.
have ginm : ~ ((g @` `I_n.+1) m).
  by move=> [i ni gim]; have := gj _ ni; rewrite gim /m ltnn.
suff : ~ surjective `I_n.+1 setT g by [].
apply/existsNP; exists m; apply/not_implyP; split => // -[k [kn mgk]].
by apply ginm; exists k.
Qed.

End infinite_nat.

Section countably_infinite_prod_nat.

Lemma infinite_prod_nat : ~ set_finite (@setT (nat * nat)).
Proof.
move=> finprod.
have {finprod} : set_finite [set (x, 0%N) | x in @setT nat].
  have : [set (x, 0%N) | x in @setT nat] `<=` setT by [].
  by move/subset_set_finite => /(_ finprod).
move=> /set_finiteP[n /card_eqP /= [f bij_f]].
apply/infinite_nat/set_finiteP; exists n; apply/card_eqP => /=.
exists (fun x => f (x, 0%N)); split => [| |a na].
- move=> a b _ _ /(inj_of_bij bij_f) fab; suff : (a, 0%N) = (b, 0%N) by case.
  by apply: fab; rewrite !in_setE; [exists a |exists b].
- move=> a [i _ <-{a}]; apply (sub_of_bij bij_f).
  by exists (i, 0%N) => //; exists i.
- have [[x y [[i _ [_{i} <-{y} af]]]]] := (sur_of_bij bij_f) _ na.
  by exists x.
Qed.

Definition nat_of_pair := fun '(n, m) => (2 ^ n * 3 ^ m)%N.

Let primes23 n m : primes (nat_of_pair (n.+1, m.+1)) = [:: 2; 3].
Proof.
set a := (X in primes X); apply: (@sorted_eq _ leq leq_trans le_anti) => //.
  by move: (sorted_primes a); rewrite ltn_sorted_uniq_leq => /andP[].
apply uniq_perm => //; first exact: primes_uniq.
move=> i; rewrite !inE; apply/idP/orP.
- rewrite mem_primes => /and3P[].
  case: i => // -[|] // -[|[_ _|i prime4 _]]; first by left.
  by rewrite Euclid_dvdM // => /orP[|]; [rewrite Euclid_dvdX|right].
  by rewrite Euclid_dvdM // => /orP[|]; rewrite Euclid_dvdX.
- case=> /eqP ->{i}.
  + by rewrite primesM // ?expn_gt0 // {a}; rewrite primesX.
  + by rewrite primesM // ?expn_gt0 // {a}; rewrite orbC primesX.
Qed.

Let prime_decomp23 n m :
  prime_decomp (nat_of_pair (n.+1, m.+1)) = [:: (2, n.+1); (3, m.+1)].
Proof.
rewrite prime_decompE primes23 /=; congr [:: (_, _); (_, _)].
- rewrite lognM ?expn_gt0 // lognX logn_prime // muln1.
  by rewrite lognX logn_prime // muln0 addn0.
- rewrite lognM ?expn_gt0 // lognX logn_prime // muln0.
  by rewrite lognX logn_prime // muln1.
Qed.

Lemma nat_of_pair_inj : {in setT &, injective nat_of_pair}.
Proof.
move=> /= [n1 m1] [n2 m2] _ _; rewrite /nat_of_pair.
have [/and4P[]|] := boolP [&& n1 != 0, m1 != 0, n2 != 0 & m2 != 0]%N.
  move: n1 m1 n2 m2 => [|n1] [|m1] [|n2] [|m2] // _ _ _ _.
  by move/(congr1 prime_decomp); rewrite 2!prime_decomp23 => -[-> ->].
rewrite !negb_and !negbK => /or4P[]/eqP ->; rewrite ?(expn0,mul1n,muln1).
- move: n2 => [/eqP|n2]; rewrite ?(expn0,mul1n).
    by rewrite eqn_exp2l // => /eqP ->.
  by move/(congr1 (dvdn 2)); rewrite ?(Euclid_dvdX,Euclid_dvdM).
- move: m2 => [/eqP|m2]; rewrite ?(expn0,muln1).
    by rewrite eqn_exp2l // => /eqP ->.
  by move/(congr1 (dvdn 3)); rewrite ?(Euclid_dvdX,Euclid_dvdM).
- move: n1 => [/eqP|n1]; rewrite ?(expn0,mul1n).
    by rewrite eqn_exp2l // => /eqP ->.
  by move/(congr1 (dvdn 2)); rewrite ?(Euclid_dvdX,Euclid_dvdM).
- move: m1 => [/eqP|m1]; rewrite ?(expn0,muln1).
    by rewrite eqn_exp2l // => /eqP ->.
  by move/(congr1 (dvdn 3)); rewrite ?(Euclid_dvdX,Euclid_dvdM).
Qed.

Lemma countable_prod_nat : countable (@setT (nat * nat)).
Proof.
by apply/countable_injective; exists nat_of_pair; exact: nat_of_pair_inj.
Qed.

Let decomp_two n : n <> 0%N -> {pq | (n == 2 ^ pq.1 * pq.2) && odd pq.2}%N.
Proof.
move: n; apply: ltn_ind => k ih /eqP k0.
have [ok|ek] := boolP (odd k).
  by exists (0%N, k) => /=; rewrite expn0 mul1n eqxx.
rewrite -dvdn2 in ek; apply/sigW => /=.
move/dvdnP : ek => [l k2l].
have l0 : l != 0%N by apply: contra k0; rewrite k2l => /eqP ->; rewrite mul0n.
have lk : (l < k)%N by rewrite k2l ltn_Pmulr // lt0n.
move/eqP in l0; have [[p q] /= /andP[lpq oq]] := ih _ lk l0.
by exists (p.+1, q) => /=; rewrite expnS -mulnA -(eqP lpq) k2l mulnC eqxx.
Qed.

Lemma countably_infinite_prod_nat : @setT (nat * nat) #= @setT nat.
Proof.
split; first exact: countable_prod_nat.
pose f := fun n => proj1_sig (decomp_two n).
exists (fun n => if decP (n =P 0%N) is right h then f _ h else (0, 0)%N).
split => // p q _ _; rewrite /f; case: decP => //= [->{p}|p0].
  case: decP => //= q0.
  by case: decomp_two => -[p1 q1] /= /andP[/eqP -> _] [_ <-]; rewrite muln0.
case: decP => //= [->{q}|q0].
  by case: decomp_two => -[p2 q2] /= /andP[/eqP -> _] [_ ->]; rewrite muln0.
case: decomp_two => -[p1 q1] /= /andP[/eqP -> _].
by case: decomp_two => -[p2 q2] /= /andP[/eqP -> _] [-> ->].
Qed.

Definition pair_of_rat (q : rat) : nat * nat :=
  let x := numq q in let y := denq q in
  (if x >= (0 : int) then `|x|.*2 else `|x|.*2.+1, `|y|.-1).

Lemma pair_of_rat_inj : {in setT &, injective pair_of_rat}.
Proof.
move=> x y _ _; rewrite /pair_of_rat.
have [x_ge0|x_gt0] := leP (0 : int) (numq x);
  have [y_ge0|y_gt0] := leP (0 : int) (numq y).
- case=> /eqP; rewrite -!muln2 eqn_mul2r => /eqP/(congr1 Posz).
  rewrite !gez0_abs// => numqxy /(congr1 S); rewrite ?(prednK,absz_gt0)//.
  move=> /(congr1 Posz); rewrite 2!absz_denq => dxy; apply/eqP.
  by rewrite rat_eqE numqxy dxy 2!eqxx.
- by case=> /(congr1 odd); rewrite /= 2!odd_double.
- by case=> /(congr1 odd); rewrite /= 2!odd_double.
- case=> /eqP; rewrite -!muln2 eqn_mul2r => /eqP/(congr1 Posz).
  rewrite !ltz0_abs// => /eqP; rewrite eqr_opp => /eqP numqxy /(congr1 S).
  rewrite ?(prednK,absz_gt0)// => /(congr1 Posz); rewrite 2!absz_denq => dxy.
  by apply/eqP; rewrite rat_eqE numqxy dxy 2!eqxx.
Qed.

Lemma countable_rat : countable (@setT rat).
Proof.
apply/countable_injective; have [f [inj_f _]] := countable_prod_nat.
exists (f \o pair_of_rat); apply: (@in_inj_comp _ _ _ _ _ xpredT) => //.
by move=> x y _ _ /inj_f; apply; rewrite inE.
exact: pair_of_rat_inj.
Qed.

Definition nat_of_rat := nat_of_pair \o pair_of_rat.

Lemma nat_of_rat_inj : {in setT &, injective nat_of_rat}.
Proof.
apply: (in_inj_comp nat_of_pair_inj pair_of_rat_inj).
by move=> q _; rewrite in_setE.
Qed.

Definition rat_of_nat : nat -> rat := inverse 0%Q setT nat_of_rat.

Lemma nat_of_ratK : {in setT, cancel nat_of_rat rat_of_nat}.
Proof.
by apply: injective_left_inverse; exact: nat_of_rat_inj.
Qed.

End countably_infinite_prod_nat.
