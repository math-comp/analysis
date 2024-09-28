From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** *** Exercices on polynomials
- Formalisation of the algebraic  part of  a                          
 simple proof that PI is irrational  described in:                   
- http://projecteuclid.org/download/pdf_1/euclid.bams/1183510788    
*)  

Section Algebraic_part.

Open Scope ring_scope.
Import GRing.Theory Num.Theory.

(** *** Parameters definitions:
- Let n na nb be  natural numbers
- Suppose nb is a non zero nat: nb != 0
- Define the corresponding rationals a , b 
- Define pi as a/b.
*)
(* to complete  for na nb*)
Variable n : nat.
(*D*)Variables na nb: nat.
Hypothesis nbne0: nb != 0%N.

Definition a:rat := (Posz na)%:~R.
Definition b:rat := 
(*D*)(Posz nb)%:~R.

Definition pi := 
(*D*)a / b.

(** *** Definition of the polynomials:
-  Look at the f definition: the factorial, the coercion nat :> R (as a Ring), etc...
- Define F:{poly rat} using bigop.
*)
Definition f :{poly rat} := 
  (n`!)%:R^-1 *: ('X^n * (a%:P -  b*:'X)^+n).

(*D*)Definition F :{poly rat} := \sum_(i < n.+1) (-1)^i *: f^`(2*i).


(** *** Prove that:
- b is non zero rational.
*)
(* Some intermediary simple theorems *)
Lemma bne0: b != 0.
(*D*)Proof. by rewrite intr_eq0. Qed.
(** *** Prove that:
-  (a -  bX) has a size of 2
*)
Lemma P1_size: size (a%:P -  b*:'X) = 2%N.
Proof.
(*D*)have hs:  size (- (b *: 'X)) = 2%N.
(*D*)  by rewrite size_opp size_scale ?bne0 // size_polyX.
(*D*)by rewrite  addrC size_addl hs ?size_polyC //;  case:(a!= 0).
Qed.

(** *** Prove that:
-  the lead_coef of (a -  bX) is -b.
*)
Lemma P1_lead_coef: lead_coef (a%:P -  b*:'X) = -b.
Proof.
(*D*)rewrite addrC lead_coefDl.
(*D*)  by rewrite lead_coefN lead_coefZ lead_coefX mulr1.
(*D*)by rewrite size_opp size_scale ?bne0 // size_polyX size_polyC; case:(a!= 0).
Qed.

(** *** Prove that:
-  the size of (a-X)^n is n.+1
*)
Lemma P_size : size ((a%:P -  b*:'X)^+n)  = n.+1.
(*D*)elim:n=>[| n0 Hn0]; first by rewrite expr0 size_polyC.
(*D*)rewrite exprS size_proper_mul.
(*D*)  by rewrite P1_size /= Hn0.
(*D*)by rewrite lead_coef_exp P1_lead_coef -exprS expf_neq0 // oppr_eq0 bne0.
Qed.

(* 2 useful lemmas for the  Qint predicat. *)
Lemma int_Qint (z:int) : z%:~R \is a Qint.
Proof. by apply/QintP; exists z. Qed.

Lemma nat_Qint (m:nat) : m%:R \is a Qint.
Proof. by apply/QintP; exists m. Qed.

(** *** Prove that:
- Exponent and composition of polynomials combine:
*)
Lemma comp_poly_exprn: 
   forall (p q:{poly rat}) i, p^+i \Po q = (p \Po q) ^+i.
(*D*)move=> p q; elim=>[| i Hi].
(*D*)  by rewrite !expr0 comp_polyC.
(*D*)by rewrite !exprS comp_polyM Hi.
Qed.


(** *** Prove that:
- f's small coefficients are zero
*)
(* Let's begin the Niven proof *)
Lemma f_small_coef0 i: (i < n)%N -> f`_i = 0.
Proof.
(*D*)move=> iltn;rewrite /f coefZ.
(*D*)apply/eqP; rewrite mulf_eq0 invr_eq0 pnatr_eq0 eqn0Ngt (fact_gt0 n) /=.
(*D*)by rewrite coefXnM iltn.
Qed.

(** *** Prove that:
- f/n! as integral coefficients 
*)

Lemma f_int i: (n`!)%:R * f`_i \is a Qint.
Proof.
(*D*)rewrite /f coefZ mulrA mulfV; last by rewrite pnatr_eq0 -lt0n (fact_gt0 n).
(*D*)rewrite mul1r; apply/polyOverP.
(*D*)rewrite rpredM ?rpredX ?polyOverX //.
(*D*)by rewrite rpredB ?polyOverC ?polyOverZ ?polyOverX // int_Qint.
Qed.

(** *** Prove that:
the f^`(i) (x) have integral values for x = 0
*)
Lemma derive_f_0_int: forall i, f^`(i).[0] \is a Qint.
Proof.
(*D*)move=> i.
(*D*)rewrite horner_coef0 coef_derivn addn0 binomial.ffactnn.
(*D*)case:(boolP (i <n)%N).
(*D*)  move/f_small_coef0 ->.
(*D*)  by rewrite mul0rn // int_Qint.
(*D*)rewrite -leqNgt.
(*D*)move/binomial.bin_fact <-.
(*D*)rewrite /f coefZ -mulrnAl -mulr_natr mulrC rpredM //; last first.
(*D*)  rewrite mulnC !natrM !mulrA  mulVf ?mul1r ?rpredM ?nat_Qint //.
(*D*)  by rewrite  pnatr_eq0 eqn0Ngt (fact_gt0 n).
(*D*)apply/polyOverP;rewrite rpredM // ?rpredX ?polyOverX //.
(*D*)by rewrite ?rpredB ?polyOverC ?polyOverZ ?polyOverX // int_Qint.
Qed.

(** *** Deduce that:
F (0) has an integral value
*)

Lemma F0_int : F.[0] \is a Qint.
Proof.
(*D*)rewrite /F horner_sum rpred_sum // =>  i _ ; rewrite !hornerE rpredM //.
(*D*)  by rewrite -exprnP rpredX.
(*D*)by rewrite derive_f_0_int.
Qed.

(** *** Then prove 
- the symmetry argument f(x) = f(pi -x).
*)
Lemma pf_sym:  f \Po (pi%:P -'X) = f.
Proof.
(*D*)rewrite /f comp_polyZ;congr (_ *:_).
(*D*)rewrite comp_polyM   !comp_poly_exprn.
(*D*)rewrite comp_polyB comp_polyC !comp_polyZ !comp_polyX scalerBr /pi.
(*D*)have h1:    b%:P * (a / b)%:P = a%:P.
(*D*)  by rewrite polyCM mulrC -mulrA -polyCM mulVf ?bne0 // mulr1.
(*D*)suff->: (a%:P - (b *: (a / b)%:P - b *: 'X)) = b%:P * 'X.
(*D*)  rewrite exprMn mulrA - exprMn [X in _ = X]mulrC.
(*D*)  congr (_ *_); congr (_^+_).
(*D*)  rewrite mulrC mulrBr; congr (_ -_)=>//.
(*D*)  by rewrite mul_polyC.
(*D*)by rewrite -!mul_polyC h1 opprB addrA addrC addrA addNr add0r.
Qed.

(** *** Prove 
- the symmetry for the derivative 
*)

Lemma  derivn_fpix i :
      (f^`(i)\Po(pi%:P -'X))= (-1)^+i *: f^`(i).
Proof.
(*D*)elim:i ; first by rewrite /= expr0 scale1r pf_sym.
(*D*)move => i Hi.
(*D*)set fx := _ \Po _.
(*D*)rewrite derivnS exprS -scalerA -derivZ -Hi deriv_comp !derivE.
(*D*)by rewrite mulrBr mulr0 add0r mulr1 -derivnS /fx scaleN1r opprK.
Qed.

(** *** Deduce that
- F(pi) is an integer 
*)
Lemma FPi_int : F.[pi] \is a Qint.
Proof.
(*D*)rewrite /F horner_sum rpred_sum //.
(*D*)move=> i _ ; rewrite !hornerE rpredM //.
(*D*)  by rewrite -exprnP rpredX.
(*D*)move:(derivn_fpix (2*i)).
(*D*)rewrite  mulnC exprM sqrr_sign scale1r => <-.
(*D*)by rewrite horner_comp !hornerE subrr derive_f_0_int.
Qed.


(** *** if you have time
- you can prove the  equality  F^`(2) + F = f 
- that is  needed by the analytic part of the Niven proof
*)

Lemma D2FDF : F^`(2) + F = f.
Proof.
(*D*)rewrite /F linear_sum /=.
(*D*)rewrite (eq_bigr (fun i:'I_n.+1 => (((-1)^i *: f^`(2 * i.+1)%N)))); last first.
(*D*)  move=> i _ ;rewrite !derivZ; congr (_ *:_).
(*D*)  rewrite -!derivnS;congr (_^`(_)).
(*D*)  by rewrite mulnS addnC addn2.
(*D*)rewrite [X in _ + X]big_ord_recl muln0 derivn0.
(*D*)rewrite -exprnP expr0 scale1r (addrC f) addrA -[X in _ = X]add0r.
(*D*)congr (_ + _).
(*D*)rewrite big_ord_recr addrC addrA -big_split big1=>[| i _].
(*D*)  rewrite add0r /=; apply/eqP; rewrite scaler_eq0 -derivnS derivn_poly0.
(*D*)    by rewrite eqxx orbT.
(*D*)  suff ->: (size f) = (n + n.+1)%N by rewrite -plus_n_O leqnSn.
(*D*)  rewrite /f size_scale; last first.
(*D*)    by rewrite invr_neq0 // pnatr_eq0 -lt0n (fact_gt0 n).
(*D*)  rewrite size_monicM ?monicXn //; last by rewrite -size_poly_eq0 P_size.
(*D*)  by rewrite  size_polyXn P_size.
(*D*)rewrite /bump /= -scalerDl.
(*D*)apply/eqP;rewrite scaler_eq0 /bump -exprnP add1n exprSr.
(*D*)by rewrite mulrN1 addrC subr_eq0 eqxx orTb.
Qed.

End Algebraic_part.

