
From mathcomp Require Import all_ssreflect all_algebra.

(* Marie's proposal: encode the "partial" properties by reasoning on
  the graph of functions. The other option would be to study a partial
  order defined on subsets of the ambiant space V, on which it is possible
  to obtain a bounded linear form extending f. But this options seems much
  less convenient, in particular when establishing that one can extend f
  on a space with one more dimension. Indeed, exhibiting a term of type
  V -> R requires a case ternary analysis on F, the new line, and an 
  explicit direct sum to ensure the definition is exhaustive. Working with
  graphs allows to leave this argument completely implicit. *)
 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.


(* A handful of axioms, stated here without trying to minimize the
   interface. *)

 Axiom Prop_irrelevance : forall (P : Prop) (x y : P), x = y.
 Axiom funext : forall (T U : Type) (f g : T -> U), (f =1 g) -> f = g.
 Axiom propext : forall (P Q : Prop), (P <-> Q) -> (P = Q).

 Definition Choice_prop := ((forall T U  (Q : T -> U -> Prop),
                                (forall t : T, exists u : U,  Q t u) -> (exists e, forall t,  Q t (e t)))) .
 Definition EM :=  forall (P : Prop), P \/ ~ P.


Section Diaconescu.
 
 Lemma contrapos (P Q : Prop) : (P -> Q) -> (~Q -> ~P).
 Proof.
   move => H nQ p.
   by pose bot := nQ (H p).
 Qed.
 
 Lemma propeqE (P Q : Prop) : (P = Q) = (P <-> Q).
 Proof. by apply: propext; split=> [->|/propext]. Qed.

 Lemma funeqE {T U : Type} (f g : T -> U) : (f = g) = (f =1 g).
 Proof. by rewrite propeqE; split=> [->//|/funext]. Qed.

 Lemma predeqE {T} (P Q : T -> Prop) : (P = Q) = (forall x, P x <-> Q x).
 Proof.
 by rewrite propeqE; split=> [->//|?]; rewrite funeqE=> x; rewrite propeqE.
 Qed.



  (*the following is directly borrowed from coq.stdlib/Coq.Logic.Diaconescu *)

 Lemma Relational_Choice  : Choice_prop ->  forall A B  (R:A->B->Prop),
    (forall x : A, exists y : B, R x y) ->
 (exists R' : A->B->Prop, subrelation R' R /\ forall x, exists! y, R' x y).
 Proof.
 move => H A B R Hex. case (H A B R Hex) => [f P].    
 exists (fun x y => y = (f x)).
 split.
 move => x y -> ; exact : (P x). 
 move => x ; exists (f x) ; split.
   by [].
   by move => z ->.
 Qed.


 Lemma rel_choice_and_proof_irrel_imp_guarded_rel_choice :
 Choice_prop -> (forall A B (P : A ->Prop), forall R : A->B->Prop,
    (forall x : A, P x -> exists y : B, R x y) ->
    (exists R' : A->B->Prop,
    subrelation R' R /\ forall x, P x -> exists! y, R' x y)).
 Proof.
  move => choice_prop.
  pose rel_choice := Relational_Choice  choice_prop. 
  move => A B P R H.
  destruct (rel_choice _ _ (fun (x:sigT P) (y:B) => R (projT1 x) y)) as (R',(HR'R,H0)).
  intros (x,HPx).
  destruct (H x HPx) as (y,HRxy).
  exists y; exact HRxy.
  set (R'' := fun (x:A) (y:B) => exists H : P x, R' (existT P x H) y).
  exists R''; split.
  intros x y (HPx,HR'xy).
    change x with (projT1 (existT P x HPx)); apply HR'R; exact HR'xy.
  intros x HPx.
  destruct (H0 (existT P x HPx)) as (y,(HR'xy,Huniq)).
  exists y; split. exists HPx; exact HR'xy.
  intros y' (H'Px,HR'xy').
    apply Huniq.
    rewrite (Prop_irrelevance  HPx H'Px); exact HR'xy'.
Qed.

 Lemma AC_bool_subset_to_bool :
  Choice_prop -> 
  (exists R : (bool -> Prop) -> bool -> Prop,
   (forall P:bool -> Prop,
      (exists b : bool, P b) ->
      exists b : bool, P b /\ R P b /\ (forall b':bool, R P b' -> b = b'))).
 Proof.
 move => choice_prop. 
  destruct ( (rel_choice_and_proof_irrel_imp_guarded_rel_choice choice_prop)    _ _
   (fun Q:bool -> Prop =>  exists y : _, Q y)
   (fun (Q:bool -> Prop) (y:bool) => Q y)) as (R,(HRsub,HR)).
    exact (fun _ H => H).
  exists R; move => P HP.
  case (HR P HP) as (y,(Hy,Huni)).
  exists y; firstorder.
Qed.
 


Theorem diaconescu : Choice_prop -> EM.
 Proof.
   move => choice_prop ; case  (AC_bool_subset_to_bool choice_prop) => [R H].
   move => P.
 set (class_of_true := fun b => b = true \/ P).
 set (class_of_false := fun b => b = false \/ P).
 (** the actual "decision": is (R class_of_true) = true or false? *)
 destruct (H class_of_true) as [b0 [H0 [H0' H0'']]].
 exists true; left; reflexivity.
 destruct H0.
 (** the actual "decision": is (R class_of_false) = true or false? *)
 destruct (H class_of_false) as [b1 [H1 [H1' H1'']]].
 exists false; left; reflexivity.
 destruct H1.
 (** case where P is false: (R class_of_true)=true /\ (R class_of_false)=false *)
 right.
 intro HP.
 assert (Hequiv : forall b:bool, class_of_true b <-> class_of_false b).
 intro b; split.
 unfold class_of_false in |- *; right; assumption.
 unfold class_of_true in |- *; right; assumption.
 assert (Heq : class_of_true = class_of_false).
 rewrite ( predeqE class_of_true class_of_false) ; exact : Hequiv. 
 apply Bool.diff_true_false.
 rewrite <- H0.
 rewrite <- H1.
  rewrite <- H0''. reflexivity.
 rewrite Heq.
 assumption.
 (** cases where P is true *)
 left; assumption.
 left; assumption.
 Qed.

         
End Diaconescu. 

 

Section Classical.

 Variable EM : forall (P : Prop), P \/ ~ P.

 Lemma double_neg_elim  (P :  Prop) : ~ ( ~ P) <-> P.
 Proof.
   split.
   - move => nnP. case : (EM P) ; first by [].
     by move => nP ; pose bot :=  nnP nP.
   - by move => p np.
 Qed.
 
 Lemma neg_exists (T : Type) (P : T -> Prop) : ~ ( exists s, ( P s)) -> forall s, ~ ( P s ). 
 Proof.
  by move => H s Ps ; have : exists s : T, P s by exists s.  
 Qed.

 Lemma contrap P Q : ( ~ P -> ~ Q) -> ( Q -> P ). 
 Proof.
  move => H p.  
  case : (EM P) ; first by [].   
  move => nQ.
  have bot :  False by exact : ((H nQ)p) .  
  by [].
 Qed.
 
 Lemma neg_forall (T : Type) (P : T -> Prop) : ~ (forall s, (P s)) -> exists s,  ~ ( P s).
 Proof.
   apply : contrap.
   move => nE. apply : (proj2 (double_neg_elim (forall s, (P s)))).
   move => s. apply : (proj1 (double_neg_elim (P s))).
   exact :  ((neg_exists nE) s).
 Qed.

 Lemma neg_impl (P Q : Prop) : ~ ( P -> Q) -> (P /\ ~Q).  
 Proof.
  move => H.
  rewrite -(propext (double_neg_elim P)). 
  apply : (Decidable.not_or (~ P) ( Q)).
  case => n.
   - have nH : (P-> Q) by move => p ; pose bot := n p.
     by pose bot :=  H nH.
   - have nH : ( P -> Q) by case : (EM P).
     by pose bot := H nH.
 Qed.

 
End Classical.  

 Local Open Scope ring_scope.
 Import GRing.Theory.
 Import Num.Theory.

Section SetPredRels.

 Variables T U : Type.
 Implicit Types f g : T -> U -> Prop.

 Definition set (A : Type) := A -> Prop.

 Definition total_on T (A : set T) (R : T -> T -> Prop) :=
   forall s t, A s -> A t -> R s t \/ R t s.

 (* Extends is just relation inclusion *)
 Definition extends f g := forall v r, f v r -> g v r.

 Lemma extends_refl f : extends f f. Proof. by []. Qed.

 Lemma extends_trans f2 f1 f3 : extends f1 f2 -> extends f2 f3 -> extends f1 f3. 
 Proof. by move=> h1 h2 v r /h1 /h2. Qed.

 (* We make use of funext and propext here. Ideally we would word on hprops. *)
 Lemma extends_antisym f g : extends f g -> extends g f -> f = g.
 Proof.
 move=> efg egf; apply: funext => v; apply: funext=> r; apply: propext; split.
 - exact: efg.
 - exact: egf.
 Qed.


 (* Functional (possibly empty or partial) graphs *)
 Definition functional f :=
   forall v r1 r2, f v r1 -> f v r2 -> r1 = r2.

 (* Graph of a function *)
 Definition graph_of (h : T -> U) v r : Prop := r = h v.

 (* The relation f includes the graph of function h on set A *)
 (* the intension is that f is the graph of a function h, which
    coincides with f on F *)
 Definition extends_fun_on (A : set T) f h := forall v, A v -> f v (h v).

End SetPredRels.







Section StrictInductiveFixpoint.
 (*We prove a fixpoint lemma for increasing functions on strictly
  inductive sets, following ALgebra by Lang*)
  (* Choice is not necessary, but EM is*)

  Variable EM :  forall P, P \/ ~ P.
  
  Variable (T : Type) ( R : T -> T -> Prop)  (f : T -> T).  

 
  Hypothesis f_incr : forall t, R t (f t).

  Hypothesis R_ref : forall t, R t t.

  Hypothesis R_trans : forall r s t, R r s -> R s t -> R r t.

  Hypothesis R_antisym : forall r s, R r s -> R s r -> r=s.

  Definition maj ( T: Type)  (R : T -> T -> Prop) A t := forall s, A s -> R s t.
 
  Definition sup A t :=  (maj R A t)/\(forall r, (maj R A r) -> R t r ).
  

  Hypothesis R_strind : (forall A : set T, total_on A R -> exists t,  sup A t).


  (*Beginning by lemmas on sets, least upper bounds and the subset relation *) 
 

  Lemma sup_uniq A r s : sup A r -> sup A s -> s  = r.
  Proof.
   move => [majr supr] [majs sups]. 
   exact (R_antisym (sups r  majr) (supr s majs)).
  Qed.   

  (* It seems that we don't need to reason on nonempy subsets, contr. to Lang*)
  (*Definition nonempty (A: set T) := exists x_0,  A x_0.*)

  Definition subset (A B: set T) := forall x, A x -> B x.

  Lemma subset_refl : forall A, subset A A. 
  Proof. by move => A s. Qed.   

  Lemma subset_trans : forall A B C, subset A B -> subset B C -> subset A C. 
  Proof. by  move => A B C HAB HBC s As; apply : HBC s (HAB s As). Qed.

  Lemma subset_antisym : forall A B, subset A B -> subset B A -> A = B.
  Proof.
   move => A B HAB HBA; apply : funext => s; apply: propext;  split.
   exact (HAB s).
   exact (HBA s).
  Qed. 

  (*An admissible subset is stable by f and contains the least upper bounds
   of its subsets*)

  Definition adm (B :set T) :=  (forall x , B x -> (B (f x)) ) /\
                              (forall C : set T, subset C B -> total_on C R ->
                                                 forall t, (sup C t -> B t)). 
  (* M is the intersection of all admissible subsets *)

  Definition M := fun x => ( forall B,  adm B -> B x).

  (* This is how we prove the existence of a fixpoint *)
  Lemma fixpoint_tot M : adm M ->  (total_on M R) -> exists t,  t = f t.
  Proof.
   move => adM totM.
   have idM : forall x,  M x -> M x  by []. 
   case : (R_strind  totM) => [t supt]. 
   exists t.
   pose Mt := (proj2 adM) M idM totM t supt.
   pose ht :=  ((proj1 supt) ((f t))) ( (proj1 adM) t  Mt).
   exact (R_antisym (f_incr t) ht) .   
  Qed.

  Lemma stabM : forall x, M x -> M (f x).
  Proof. move => x Mx B admB ;  exact ((proj1 admB) x  (Mx B admB)). Qed.

  (*To prove that M is itself admissible, we must now show that it contains 
    the least upper bounds of its totally ordered subsets*)

  Lemma BsubsetM : forall B, adm B -> subset M B. Proof.
  by move => B admB x Mx ; apply : Mx B admB.
  Qed.

  Lemma adm_M : adm M. 
  Proof.
  split.
  - exact : stabM.
  - move => C MC totC ; move : (R_strind totC) => [t tsupC] r rsupC.
    rewrite (sup_uniq tsupC rsupC)  => B [f_B sup_int_B].
    have BC : subset C B by  move => x Cx ; apply : (MC x Cx B).  
    exact : (sup_int_B C BC totC). 
  Qed.

 (* To prove totality of M we need a few lemmas*)

  Definition extreme c :=  M c /\ (forall (x:T), M x -> ((x <> c) ->  R x c-> R (f x) c)).

  Lemma extrM : subset extreme M.
  Proof. by move => x extrx ; apply : proj1 extrx. Qed.

  Definition extr_set c :=  fun x => (M x /\ ((R x c) \/ ( R (f c) x))).   

  Lemma subextrM (c :T) : extreme c -> subset (extr_set c) M.
  Proof.
   move =>  extrc x  extrcx ; exact (proj1 extrcx).
  Qed.


  Lemma MextrM c :  extreme c -> (forall x , M x -> extr_set c x).  
  Proof. 
  move =>  [Mc extrc].
  have extrMc : extreme c. split ; first by exact : Mc.
                          exact : extrc.  
  have extr_adm : adm (extr_set c). 
  split.
  - move => x [Mx extrcx] ; case : (EM (x =c)).
    - move => H ; split.
      exact  (stabM  Mx).
      by  right; rewrite H.
    - move => neq_xc ; case : extrcx.
       - move => Rxc ; split.
          - exact : stabM.
          - left ;   exact (extrc x Mx neq_xc   Rxc). 
          - move => Rfcx ; split.
            - exact : stabM.
            - right; exact : (R_trans  Rfcx (f_incr x)).  
   - move => C Cextrc totC t supCt.
     split. 
     - exact: (proj2 adm_M C (subset_trans Cextrc ((subextrM extrMc) )) totC t supCt).
     - case : (EM  (maj R C c)).
       - move => H ; left ; exact : (proj2 supCt c H). 
       - move =>  /(neg_forall EM)-[s ps]. 
         have [Cs nRsc] := neg_impl EM ps => {ps}. (*short*) 
         have lem : R (f c) s .
         case : (EM (R ( f c) s )) ; first  by [].
          case : (proj2  (Cextrc s Cs)).
            - move =>  H ; pose bot := nRsc H; by []. 
            - by [].   
         right. exact : (R_trans lem (proj1 supCt s Cs)).     
  move => x mx. exact : ( mx (extr_set c) extr_adm).
  Qed.


  Lemma all_extr : forall c,  M c -> extreme c.  
  Proof.
   have admE : adm extreme. 
    have f_E : forall c,  extreme c -> extreme ( f c ). 
      move => c  [Mc extrc]. split. by  apply : stabM.
      have  extrec : extreme c. split. by []. by [].
      move => x Mx neq_xfc. 
        case : (proj2 (MextrM extrec  Mx)).
        case : (EM (x =c )).
         - by  move => -> .
         - move => neq_xc Rxc Rxfc ;
                     exact ( R_trans (extrc x Mx neq_xc Rxc) (f_incr c)).
         - by move => Rfcx Rxfc ; pose bot := (neq_xfc (R_antisym Rxfc Rfcx)).
    have sup_E : (forall C , subset C extreme -> total_on C R ->
                                    forall t, (sup C t -> extreme t)). 
      move => C subCE totC t supCt.
      have Mt : M t
        by apply : (proj2 adm_M) C (subset_trans subCE extrM) totC t supCt.
      split. exact: Mt.  
        move => x Mx neq_xt Rxt.    
        case : (EM (forall c, C c -> R (f c) x )). 
         - move => H.
           have lem : maj R C x. move => c Cc ; exact : ( R_trans (f_incr c) (H c Cc)).
           by pose bot := neq_xt (R_antisym Rxt (proj2 supCt x lem)). 
         - move => /(neg_forall EM)-[c H1]. pose H2 := neg_impl EM H1.
           move : H2 ; move => [Cc nRfcx] {H1}. (*short ?*) 
           have extrec : extreme c by apply :subCE c Cc.
           case : (proj2 ( MextrM  extrec  Mx)).
             - case : (EM (x =c)).
               - move => eq_xc ; move : neq_xt ; rewrite eq_xc => neq_ct.
                 move : extrec. rewrite -eq_xc  => extrx.
                 case : (proj2 (MextrM extrx Mt)).
                   - move : neq_ct; rewrite -eq_xc => neq_xt. (*short*)
                     by move => Rtx; pose bot := neq_xt (R_antisym Rxt Rtx).
                   - by [].
               - move => neq_xc Rxc.
                 exact : (R_trans ((proj2 extrec) x Mx neq_xc Rxc) (proj1 supCt c Cc)) .
             - move => Rfcx ; by pose bot := nRfcx Rfcx.               
   split. 
     exact : f_E. 
     exact : sup_E.     
  by move => c Mc; exact : (Mc extreme admE). 
  Qed.


  (*Now we can prove totality of R on M and conclude *)
  Lemma tot_M : total_on M R. 
  Proof.
   move => x y Mx My.
   case :  (proj2 (MextrM (all_extr Mx) My)).
     by  move => Ryx ; right.
     by move => Rfxy ; left ;  apply :  R_trans (f_incr x) Rfxy.    
  Qed.


  Lemma fixpoint : exists t,  t = f t. 
  Proof.
   exact (fixpoint_tot adm_M tot_M).
  Qed.


End StrictInductiveFixpoint.  



Section Zorn.


 (*This proof of Zorn using the fixpoint theorem follows Lang, Algebra, Appendix 2*)
  (* We first prove Zorn for strictly inductive sets*)

 Variable Choice_prop :  forall T U (P : T -> U -> Prop),
     (forall t : T, exists u : U,  P t u) -> (exists e, forall t,  P t (e t)).

 Variable EM :  forall P, P \/ ~P.
   
 Lemma Zorn_strict : forall (T : Type) ( R : T -> T -> Prop), 
   (forall t, R t t) -> (forall r s t, R r s -> R s t -> R r t) ->
   (forall s t, R s t -> R t s -> s = t) ->
   (forall A : set T, total_on A R -> exists t,
         (maj R A t)/\(forall r, (maj R A r) -> R t r )) ->
   exists t, forall s, R t s -> s = t.
 Proof.
  move =>  T R Hrefl Htrans Hord Hchain.
  case : (EM (exists t, forall s: T, R t s -> s= t)) ; first by [].
  move => /neg_exists Habs.  
  have Hsucc :  (forall t, exists s, R t s /\ t <> s).
    move => t.  case : (EM ( exists s : T, R t s /\ t <> s)) ; first by [].
    move => /neg_exists H.
    have lem : (forall s : T, R t s -> s=t).
      move => s Rts. case : (EM (t=s)) ; first by [].
      move => sneqt ; have lem2 : (R t s /\ t <> s) by split .
      by  have bot := H s lem2.
  by have bot := Habs t lem. 
  case : (Choice_prop Hsucc) => {Hsucc} f Hf ; have Hmaj := fun a => proj1 (Hf a). 
   pose Hfix := fixpoint EM Hmaj Hrefl Htrans Hord Hchain.   
   case : Hfix => t hfix. 
     by have bot := (proj2 (Hf t) hfix ).
 Qed. 



 (*Then we deduce the more general Zorn Lemma for orders.
  This is done by applying Zorn_strict to the totally ordered subsets of T
  ordered by inculsion *)


 Variable ( T : Type) ( R : T -> T -> Prop).

 Record tot_subset : Type := Tot_subset
                              {car : set T ; tot : total_on car R}.

 Lemma tot_subset_eq U1 U2 : car U1 = car U2 -> U1 = U2.
 Proof.
  case: U1 => m1 pm1; case: U2 => m2 pm2 /= e;
                                    move: pm1 pm2; rewrite e => pm1 pm2.
 by congr Tot_subset; apply: Prop_irrelevance.
 Qed.



 Definition subsett ( C D : tot_subset) := subset (car C) (car D). 
  
 Lemma  Zorn : 
   (forall t, R t t) -> (forall r s t, R r s -> R s t -> R r t) ->
   (forall s t, R s t -> R t s -> s = t) ->
   (forall A : set T, total_on A R -> exists t, forall s, A s -> R s t) ->
   exists t, forall s, R t s -> s = t.
 Proof.
 move => Rrefl Rtrans Rantis Rind.
 have subset_strict_ind :  (forall W : set (tot_subset), total_on W subsett ->
     exists A, (maj subsett W A)/\(forall B, (maj subsett W B) -> subsett A B )).
  move => W Htot. 
  pose U := fun (t : T) => exists A, (W A) /\ (car A t). 
  have tot_U : total_on U R. 
   move => t s [[cAt tot_At] [Wt ct]] [[cAs tot_As] [Ws cs]].
   case:  (Htot (Tot_subset tot_At) (Tot_subset tot_As) Wt Ws).
     by  move => Ats ; exact (tot_As  t s  (Ats t ct) cs). 
     by  move => Ast ;  rewrite or_comm ;  exact  (tot_At s t (Ast s cs) ct).  
  pose Utot := Tot_subset tot_U.
  have UsupW : (maj subsett W Utot)/\
               (forall B, (maj subsett W B) -> subsett Utot B).
    split ; first  by  move => B WB tB ctB //= ; exists B ; split.  
    move => B majWB t //= [A [ ]] WA cAt ; exact (majWB A WA t cAt). 
  by  exists Utot. 
 have subsett_maj : exists (A : tot_subset),
                    forall (B : tot_subset), subsett A B -> B = A. 
 apply : Zorn_strict.
  by move => t; apply : subset_refl. 
  by move => r s t ; apply : subset_trans. 
  by move => s t Hst Hts ; apply : tot_subset_eq ; apply : subset_antisym.
  exact : subset_strict_ind. 
 case : subsett_maj => [[cA PA]] majA.
 pose tot_A := Tot_subset PA.
 (*we want to handle A as a subset and as a totally ordered subset *) 
 case : (Rind cA PA) => t t_maj.
 exists t ; move => s Rts.
 pose B := fun u => (cA u)\/(u=s).
 have lem : total_on B R. 
  move => u v Bu Bv ; case : Bv; case :  Bu.    
    exact :  PA.
    by move => -> Av ; right ; apply :  Rtrans v t s (t_maj v Av) Rts.
    by move => Au -> ; left ; apply : Rtrans u t s (t_maj u Au) Rts.  
    by move => -> -> ; left ;apply : Rrefl s. 
 pose tot_B := Tot_subset lem. 
 have HAB : subsett tot_A tot_B by move => u Au ; left. 
 have eq_A_B : tot_B = tot_A  by apply : majA tot_B HAB. 
 have eqc_A_B : cA = B.
  have lem1 : B = car (tot_B) by [] ; rewrite lem1.
  have lem2 : cA = car (tot_A) by [] ; rewrite lem2 .
  by rewrite eq_A_B  => {lem1} {lem2}. 
 have As : cA s. 
   have Bs : B s by right .
   by rewrite eqc_A_B.
 exact : Rantis s t (t_maj s As) Rts. 
 Qed. 
   
End Zorn.
 





Section OrderRels.

 Variable (R : numDomainType).

 (* Upper bound *)
 Definition ubd (s : set R) (a : R) := forall x, s x -> x <= a.

 (* Lower bound *)
 Definition ibd (s : set R) (a : R) := forall x, s x -> a <= x.

 (* the intension is that f is the graph of a function bounded by p *)
 Definition maj_by T p (f : T -> R -> Prop) :=
   forall v r, f v r -> r <= p v.

 End OrderRels.  


 Section LinAndCvx.

 Variables (R : numDomainType) (V : lmodType R).

 Definition convex (p : V -> R) :=  forall v1 v2 l m,
   ( 0 <= l /\ 0 <= m) ->  l + m = 1 -> p (l *: v1 + m *: v2) <= l * (p v1) + m * (p v2).

 Definition linear_rel (f : V -> R -> Prop) :=
   forall v1 v2 l r1 r2,  f v1 r1 -> f v2 r2 -> f (v1 + l *: v2) (r1 + l * r2).

 Variable f : V -> R -> Prop.
 Hypothesis lrf : linear_rel f.

 Lemma linrel_00 x r : f x r -> f 0 0.
 Proof.
 suff -> : f 0 0 = f (x + (-1) *: x) (r + (-1) * r) by move=> h; apply: lrf.
 by rewrite scaleNr mulNr mul1r scale1r !subrr.
 Qed.

 Lemma linrel_scale x r l : f x r -> f (l *: x) (l * r).
 Proof.
 move=> fxr.
 have -> : f (l *: x) (l * r) = f (0 + l *: x) (0 + l * r) by rewrite !add0r.
 by apply: lrf=> //; apply: linrel_00 fxr.
 Qed.

 Lemma linrel_add x1 x2 r1 r2 : f x1 r1 -> f x2 r2 -> f (x1 - x2)(r1 - r2).
 Proof.  
     have -> : x1 - x2 = x1 + (-1) *: x2 by rewrite scaleNr scale1r.
     have -> : r1 - r2 = r1 + (-1) * r2 by rewrite mulNr mul1r.
     by apply: lrf.
 Qed.


 Definition add_line f w a := fun v r =>
   exists v' : V, exists r' : R, exists lambda : R,
         [/\ f v' r', v = v' + lambda *: w & r = r' + lambda * a].

 End LinAndCvx.


 Section HBPreparation.
 
 Variable EM : forall P, P \/ ~ P.

 Variable Choice_prop :  forall T U (P : T -> U -> Prop),
     (forall t : T, exists u : U,  P t u) -> (exists e, forall t,  P t (e t)).
 
 Variables (R : realFieldType) (V : lmodType R).

 Variables (F G : set V) (phi : V -> R) (p : V -> R).

Hypothesis linphiF : forall v1 v2 l, F v1 -> F v2 -> 
                              phi (v1 + l *: v2) = phi v1 + l * (phi v2).

 Implicit Types (f g : V -> R -> Prop).

 Hypothesis F0 : F 0.

Fact phi0 : phi 0 = 0.
Proof.
have -> : 0 = 0 + (-1) *: 0 :> V by rewrite scaler0 addr0.
by rewrite linphiF // mulN1r addrN.
Qed.

 Hypothesis p_cvx : convex p.

 Hypothesis sup : forall (A : set R) (a m : R),
     A a -> ubd A m ->
     {s : R | ubd A s /\ forall u, ubd A u -> s <= u}. 

 Hypothesis inf : forall (A : set R) (a m : R),
     A a ->  ibd A m ->
     {s : R | ibd A s /\ forall u, ibd A u -> u <= s}.

 (* f is a subset of (V x R), if v is in pi_1 f, then (v, phi v) is in f.
    Otherwise said, the graph of phi restructed to pi_1 f is included in f*)

 Definition prol f := forall v, F v -> f v (phi v).

 Definition spec (f : V -> R -> Prop) :=
   [/\ functional f, linear_rel f, maj_by p f &  prol f].

 Record zorn_type : Type := ZornType
   {carrier : V -> R -> Prop; specP : spec carrier}.

 Hypothesis spec_phi : spec (fun v r => F v /\ r = phi v).

 Definition zphi := ZornType spec_phi.

 Lemma zorn_type_eq z1 z2 : carrier z1 = carrier z2 -> z1 = z2.
 Proof.
 case: z1 => m1 pm1; case: z2 => m2 pm2 /= e; move: pm1 pm2; rewrite e => pm1 pm2.
 by congr ZornType; apply: Prop_irrelevance.
 Qed.

 Definition zorn_rel (z1 z2 : zorn_type) := extends (carrier z1) (carrier z2).

 Lemma zorn_rel_refl z : zorn_rel z z.
 Proof. rewrite /zorn_rel. exact: extends_refl. Qed.  

 Lemma zorn_rel_trans z1 z2 z3 :
   zorn_rel z1 z2 -> zorn_rel z2 z3 -> zorn_rel z1 z3.
 Proof. rewrite /zorn_rel; exact: extends_trans. Qed.

 Lemma zorn_rel_antisym z1 z2 : zorn_rel z1 z2 -> zorn_rel z2 z1 -> z1 = z2.
 Proof.
 rewrite /zorn_rel /= => s12 s21; apply: zorn_type_eq; exact: extends_antisym.
 Qed.

 Lemma zorn_rel_maj (A : set zorn_type) : total_on A zorn_rel ->
    exists t, forall s, A s -> zorn_rel s t.
 Proof.
 move=> htot.
 case: (EM (exists a, A a)) => [[w Aw] | eA]; last first.  
   by exists zphi => a Aa; elim: eA; exists a.  
 (* g is the union of the graphs indexed by elements in a *)
 pose g v r := exists a, A a /\ (carrier a v r).
 have g_fun : functional g.
   move=> v r1 r2 [a [Aa avr1]] [b [Ab bvr2]].
   have [] : zorn_rel a b \/ zorn_rel b a by exact: htot.  
   - rewrite /zorn_rel; case: b Ab bvr2 {Aa} => s2 [fs2 _ _ _] /= _ s2vr2 ecas2.
     by move/ecas2: avr1 => /fs2 /(_ s2vr2).
   - rewrite /zorn_rel; case: a Aa avr1 {Ab} => s1 [fs1 _ _ _] /= _ s1vr1 ecbs1.
     by move/ecbs1: bvr2; apply: fs1.
 have g_lin : linear_rel g. 
   move=> v1 v2 l r1 r2 [a1 [Aa1 c1]] [a2 [Aa2 c2]].
   have [sc12 | sc21] := htot _ _ Aa1 Aa2.
   - have {c1 sc12 Aa1 a1} c1 :  carrier a2 v1 r1 by apply: sc12.
     exists a2; split=> //; case: a2 {Aa2} c2 c1 => c /= [_ hl _ _] *; exact: hl.
   - have {c2 sc21 Aa2 a2} c2 :  carrier a1 v2 r2 by apply: sc21.
     exists a1; split=> //; case: a1 {Aa1} c2 c1 => c /= [_ hl _ _] *; exact: hl.
 have g_majp : maj_by p g by move=> v r [[c [fs1 ls1 ms1 ps1]]] /= [_ /ms1].  
 have g_prol : prol g.
   move=> *; exists w; split=> //; case: w Aw => [c [_ _ _ hp]] _ //=; exact: hp.
 have spec_g : spec g by split.
 pose zg := ZornType spec_g.
 by exists zg => [a Aa]; rewrite /zorn_rel /= => v r cvr; exists a.  
 Qed.

 Lemma zorn_rel_ex : exists g : zorn_type, forall z, zorn_rel g z -> z = g.
 Proof.
 apply: Zorn.
 - exact : Choice_prop.  
 - exact : EM.
 - exact: zorn_rel_refl.
 - exact: zorn_rel_trans.
 - exact: zorn_rel_antisym.
 - exact: zorn_rel_maj.
 Qed.

 Variable g : zorn_type.

 Hypothesis gP : forall z, zorn_rel g z -> z = g.

 (*The next lemma proves that when z is of zorn_type, it can be extended on any
  real line directed by an arbitrary vector v *)

 Lemma domain_extend  (z : zorn_type) v :
     exists2 ze : zorn_type, (zorn_rel z ze) & (exists r, (carrier ze)  v r).
 Proof.
 case: (EM (exists r, (carrier z v r))).
   by case=> r rP; exists z => //; exists r.
 case: z => [c [fs1 ls1 ms1 ps1]] /= nzv.
 have c00 : c 0 0.
   rewrite -phi0; exact: ps1.
 have [a aP] : exists a,  forall (x : V) (r lambda : R),
       c x r -> r + lambda * a <= p (x + lambda *: v).
   suff [a aP] : exists a,  forall (x : V) (r lambda : R),
       c x r -> 0 < lambda ->
       r + lambda * a <= p (x + lambda *: v) /\
       r - lambda * a <= p (x - lambda *: v).
     exists a=> x r lambda cxr.
     have {aP} aP := aP _ _ _ cxr.
     case: (ltrgt0P lambda) ; [by case/aP | move=> ltl0 | move->]; last first.
       by rewrite mul0r scale0r !addr0; apply: ms1. 
     rewrite -[lambda]opprK scaleNr mulNr. 
     have /aP [] : 0 < - lambda by rewrite oppr_gt0. 
     done.
   pose b (x : V) r lambda : R := (p (x + lambda *: v) - r) / lambda.
   pose a (x : V) r lambda : R := (r - p (x - lambda *: v)) / lambda.
   have le_a_b x1 x2 r1 r2 s t : c x1 r1 -> c x2 r2 -> 0 < s -> 0 < t ->
                                 a x1 r1 s <= b x2 r2 t.
     move=> cxr1 cxr2 lt0s lt0t; rewrite /a /b.
     rewrite ler_pdivl_mulr // mulrAC ler_pdivr_mulr // mulrC [_ * s]mulrC.
     rewrite !mulrDr !mulrN ler_subl_addr addrAC ler_subr_addr. 
     have /ler_pmul2r <- : 0 < (s + t) ^-1 by rewrite invr_gt0 addr_gt0.
     set y1 : V := _ + _ *: _; set y2 : V :=  _ - _ *: _. 
     set rhs := (X in _ <= X).
     have step1 : p (s  / (s + t) *: y1 + t  / (s + t) *: y2) <= rhs.
       rewrite /rhs !mulrDl ![_  * _ / _]mulrAC; apply: p_cvx.
       split.
        rewrite divr_ge0 //=. 
          by apply : ltW.
          by rewrite addr_ge0 //= ; apply: ltW.
        rewrite divr_ge0 //=.    
          by apply : ltW.
          by rewrite  addr_ge0 //= ;  apply: ltW.    
     by rewrite -mulrDl mulfV //; apply: lt0r_neq0; rewrite addr_gt0.
     apply: le_trans step1 => {rhs}.
     set u : V := (X in p X).
     have {u y1 y2} -> : u = t  / (s + t) *: x1 + s / (s + t) *: x2.
       rewrite /u ![_ / _]mulrC -!scalerA -!scalerDr /y1 /y2; congr (_ *: _).
       by rewrite !scalerDr addrCA scalerN scalerA [s * t]mulrC -scalerA addrK.
     set l := t / _; set m := s / _; set lhs := (X in X <= _).
     have {lhs} -> : lhs = l * r1 + m * r2.
       by rewrite /lhs mulrDl ![_  * _ / _]mulrAC.
     apply: ms1; apply: (ls1) => //.
     rewrite -[_ *: _]add0r -[_ * _] add0r; apply: ls1 => //.
     pose Pa : set R := fun r =>  exists x1, exists r1, exists s1,
       [/\ c x1 r1, 0 < s1 & r = a x1 r1 s1].   
     pose Pb : set R := fun r =>  exists x1, exists r1, exists s1,
       [/\ c x1 r1, 0 < s1 & r = b x1 r1 s1].   
     have exPa : Pa (a 0 0 1) by exists 0; exists 0; exists 1; split.
     have exPb : Pb (b 0 0 1) by exists 0; exists 0; exists 1; split.
     have majPa x : Pa x -> x <= b 0 0 1. 
       move=> [y [r [s [cry lt0s ->]]]]; apply: le_a_b => //; exact: ltr01.
     have minPb x : Pb x -> a 0 0 1 <= x. 
       move=> [y [r [s [cry lt0s ->]]]]; apply: le_a_b => //; exact: ltr01.
     have [sa [ubdP saP]]:= sup exPa majPa; have [ib [ibdP ibP]]:= inf exPb minPb.
     have le_sa_ib : sa <= ib.
       apply: saP=> r' [y [r [l [cry lt0l -> {r'}]]]].
       apply: ibP=> s' [z [s [m [crz lt0m -> {s'}]]]]; exact: le_a_b.
     pose alpha := ((sa + ib) / 2%:R).
     have le_alpha_ib : alpha <= ib by rewrite /alpha midf_le.
     have le_sa_alpha : sa <= alpha by rewrite /alpha midf_le.
     exists alpha => x r l cxr lt0l; split.
     - suff : alpha <= b x r l.          
         by rewrite /b; move/ler_pdivl_mulr: lt0l->; rewrite ler_subr_addl mulrC. 
       by apply: le_trans le_alpha_ib _; apply: ibdP; exists x; exists r; exists l.
     - suff : a x r l <= alpha.          
         rewrite /a. move/ler_pdivr_mulr: lt0l->.
         by rewrite ler_subl_addl -ler_subl_addr mulrC. 
       by apply: le_trans le_sa_alpha; apply: ubdP; exists x; exists r; exists l.
 pose z' := add_line c v a.
 have z'_extends :  extends c z'.
   move=> x r cxr; exists x; exists r; exists 0; split=> //.
   - by rewrite scale0r addr0.
   - by rewrite mul0r addr0.
 have z'_prol : prol z'.
   move=> x /ps1 cxphix; exists x; exists (phi x); exists 0; split=> //.
   - by rewrite scale0r addr0.
   - by rewrite mul0r addr0.
 - have z'_maj_by_p : maj_by p z'.
   by move=> x r [w [s [l [cws -> ->]]]]; apply: aP.
 - have z'_lin : linear_rel z'.
   move=> x1 x2 l r1 r2 [w1 [s1 [m1 [cws1 -> ->]]]] [w2 [s2 [m2 [cws2 -> ->]]]].
   set w := (X in z' X _); set s := (X in z' _ X).
   have {w} -> : w = w1 + l *: w2 + (m1 + l * m2) *: v.
     by rewrite /w !scalerDr !scalerDl scalerA -!addrA [X in _ + X]addrCA.
   have {s} -> : s = s1 + l * s2 + (m1 + l * m2) * a.
     by rewrite /s !mulrDr !mulrDl mulrA -!addrA [X in _ + X]addrCA.
   exists (w1 + l *: w2); exists (s1 + l * s2); exists (m1 + l * m2); split=> //.
   exact: ls1.  
 - have z'_functional : functional z'.
   move=> w r1 r2 [w1 [s1 [m1 [cws1 -> ->]]]] [w2 [s2 [m2 [cws2 e1 ->]]]].
   have h1 (x : V) (r l : R) : x = l *: v ->  c x r -> x = 0 /\ l = 0.
     move=> -> cxr; case: (l =P 0) => [-> | /eqP ln0]; first by rewrite scale0r. 
     suff cvs: c v (l^-1 * r) by elim:nzv; exists (l^-1 * r).
     suff -> : v = l ^-1 *: (l *: v) by exact: linrel_scale. 
     by rewrite scalerA mulVf ?scale1r.
   have [rw12 erw12] : exists r,  c (w1 - w2) r.
     exists (s1 + (-1) * s2).
     have -> : w1 - w2 = w1 + (-1) *: w2 by rewrite scaleNr scale1r.
     by apply: ls1.
   have [ew12 /eqP]: w1 - w2 = 0 /\ (m2 - m1 = 0).
     apply: h1 erw12; rewrite scalerBl; apply/eqP; rewrite subr_eq addrC addrA.
     by rewrite -subr_eq opprK e1.
   suff -> : s1 = s2 by rewrite subr_eq0=> /eqP->.
   by apply: fs1 cws2; move/eqP: ew12; rewrite subr_eq0=> /eqP<-.
 have z'_spec : spec z' by split.
 pose zz' := ZornType z'_spec.
 exists zz'; rewrite /zorn_rel => //=; exists a; exists 0; exists 0; exists 1.
 by rewrite add0r mul1r scale1r add0r; split.
 Qed.

 Lemma tot_g v : exists r, carrier g v r.
 Proof.
 have [z /gP sgz [r zr]]:= domain_extend g v.
 by exists r; rewrite -sgz.
 Qed.


Lemma hb_witness : exists h : V -> R, forall v r, carrier g v r <-> (h v = r).
Proof.
have [h hP] : exists h,  forall v, carrier g v (h v) by exact: Choice_prop tot_g.
exists h => v r.
split; last by move<-.
case: g gP tot_g hP => c /= [fg lg mg pg] => gP' tot_g' hP cvr.
by have -> // := fg v r (h v).
Qed.


End HBPreparation.


Section HahnBanach.
(* Now we prove HahnBanach on functions*)
(* We consider R a real (=ordered) field with supremum, and V a (left) module
   on R. We do not make use of the 'vector' interface as the latter enforces
   finite dimension. *)
Variable EM : forall P,  P \/ ~P.

Variable Choice_prop :  forall T U (P : T -> U -> Prop),
     (forall t : T, exists u : U,  P t u) -> (exists e, forall t,  P t (e t)).
  
Variables (R : realFieldType) (V : lmodType R).

Hypothesis sup : forall (A : set R) (a m : R),
    A a -> ubd A m ->
    {s : R | ubd A s /\ forall u, ubd A u -> s <= u}. 

(* This could be obtained from sup but we are lazy here *)
Hypothesis inf : forall (A : set R) (a m : R),
    A a ->  ibd A m ->
    {s : R | ibd A s /\ forall u, ibd A u -> u <= s}.

(* F and G are of type V -> bool, as required by the Mathematical Components
   interfaces. f is a linear application from (the entire) V to R. *)
Variables (F G : pred V) (f : V -> R) (p : V -> R).

(* MathComp seems to lack of an interface for submodules of V, so for now
   we state "by hand" that F is closed under linear combinations. *)
Hypothesis F0 : F 0.
Hypothesis linF : forall v1 v2 l, F v1 -> F v2 -> F (v1 + l *: v2).

Hypothesis linfF : forall v1 v2 l, F v1 -> F v2 -> 
                              f (v1 + l *: v2) = f v1 + l * (f v2).

(* In fact we do not need G to be a superset of F *)
(* Hypothesis sFG : subpred F G. *)

Hypothesis p_cvx : convex p.

Hypothesis f_bounded_by_p : forall x, F x -> f x <= p x.

Theorem HahnBanach : exists g : {scalar V}, 
  (forall x,  g x <= p x) /\ (forall x, F x -> g x = f x).
pose graphF v r := F v /\ r = f v.
have func_graphF : functional graphF by move=> v r1 r2 [Fv ->] [_ ->].
have lin_graphF : linear_rel graphF.
  move=> v1 v2 l r1 r2 [Fv1 ->] [Fv2 ->]; split; first exact: linF.
  by rewrite linfF.
have maj_graphF : maj_by p graphF by move=> v r [Fv ->]; exact: f_bounded_by_p.

have prol_graphF : prol F f graphF by move=> v Fv; split.
have graphFP : spec F f p graphF by split.
have [z zmax]:= zorn_rel_ex EM Choice_prop graphFP.
pose FP v : Prop := F v.
have FP0 : FP 0 by [].
have [g gP]:= hb_witness EM Choice_prop linfF FP0 p_cvx sup inf zmax.
have scalg : lmorphism_for *%R g.
  case: z {zmax} gP=> [c [_ ls1 _ _]] /= gP.
  have addg : additive g. 
     move=> w1 w2;  apply/gP. 
     apply: linrel_add.  exact ls1.  
       by apply /gP. 
       by apply /gP.
suff scalg : scalable_for  *%R g by split.
  by move=> w l; apply/gP; apply: linrel_scale=> //; apply/gP.
exists (Linear scalg) => /=.
have grxtf v : F v -> g v = f v.
  move=> Fv; apply/gP; case: z {zmax gP} => [c [_ _ _ pf]] /=; exact: pf.  
  suff pmajg v :  g v <= p v by split.
    by  case: z {zmax} gP => [c [_ _ bp _]] /= gP; apply/bp/gP.
Qed.

End HahnBanach.










