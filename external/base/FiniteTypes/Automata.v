Require Import FinTypes.
(**  Proofs about DFA as a test for the finType library *)
Set Implicit Arguments.
Unset Printing Implicit Defensive.
Unset Strict Implicit.
Set Contextual Implicit.

(** * Conversion between Props and bools *)

Coercion toProp (b:bool) := if b then True else False.

Instance toProp_dec b : dec (toProp b).
Proof.
  destruct b; auto.
Qed.

Section DFA.
  (** * Definition of the alphabet, words and dfa*)
  Variable Sig: finType.
  Definition word := list Sig.
  
Record dfa: Type :=
  DFA {
      S:> finType;
      s: S;
      F: decPred S;
      delta_S: S -> Sig -> S
    }.

Section Reachability.
Variable  A : dfa.
(** transition function for whole words *)
Fixpoint delta_star (q: A) (w: word) :=
  match w with 
  | nil => q
  | x::w' => delta_star (delta_S q x) w'
  end.

(** Definition if acceptance *)
Definition accept (w:word) := F (@delta_star s w).

Instance accept_dec w : dec (accept w).
Proof.
  auto.
Qed.

(** * Reachability 
- normal reachability
- reachability with a specific word
 *)

Inductive reachable (q: A) :  A -> Prop :=
| refl: reachable q q
| step q' x: reachable (delta_S q x) q' -> reachable q q'.

Definition reachable_with q w q':= delta_star q w = q'.

Hint Constructors reachable.

Lemma reachable_with_reachable (q q': A): reachable q q' <-> exists w, reachable_with q w q'.
Proof.
  split.
  - intro R. induction R.
    + now exists nil.
    + destruct IHR as [w IHR]. exists (x::w). unfold reachable_with. cbn. congruence.
  - intros [w H]. revert q H.  induction w; intros q H.
    + now rewrite H.
    + econstructor 2. apply IHw. apply H.
Qed.

Hint Resolve reachable_with_reachable.

Lemma reachable_transitive (q:A) q' q'': reachable q q' /\ reachable q' q'' -> reachable q q''.
Proof.
  intros [R R']. induction R; eauto.
Qed.
(*
Lemma reachable_delta_star q w: reachable q (delta_star q w).
Proof.
  apply reachable_with_reachable. now exists w.
Qed.
*)
(** * Reach (set of all reachable states)
- defined using fixed-point iteration *)

(* The predicate for the fixed-point iteration *)
Definition step_reach (set: list A) (q: A) := exists q' x, q' el set /\ reachable_with q' [x] q.

Lemma step_reach_consistent: step_consistent step_reach.
Proof.
  intros B q H B' sub. destruct H as [q' [x [E R]]]. exists q', x. auto.
Qed.    

Definition reach (q: A) := FCIter step_reach [q].

Lemma reach_least_fp q: least_fp_containing (FCStep step_reach) (reach q) [q]. 
Proof.
  apply step_consistent_least_fp. apply step_reach_consistent.
Qed.

Lemma reach_correct1 (q:A): inclp (reach q) (reachable q).
Proof.
  apply FCIter_ind.
  - intro x. cbn. now intros [[]|[]].
  - intros set q' H [q'' [x [E  H1]]]. eapply reachable_transitive; split.
    + apply (H _ E).
    + apply reachable_with_reachable. eauto.
Qed.
 
Lemma reach_correct2' q q': q' el reach q -> forall q'', reachable q' q'' -> q'' el reach q.
Proof.
 intros E q'' R. induction R.
  - exact E.
  - apply IHR. apply Closure_FCIter. now  exists q0, x.
Qed.

Lemma reach_correct2 q: forall q', reachable q q' -> q' el reach q.
Proof.
apply reach_correct2'. now apply preservation_FCIter.
Qed.        

Lemma reach_correct q q': reachable q q' <-> q' el (reach q).
Proof.
  split.
  - apply reach_correct2.
  - apply reach_correct1.
Qed.

Global Instance reachable_dec q q': dec (reachable q q').
Proof.
  eapply dec_prop_iff.
  - symmetry. apply reach_correct.
  - auto.
Qed.    

Global Instance reachable_with_something_dec q q': dec (exists w, reachable_with q w q').
Proof.
  eauto.
Qed.

Lemma reach_reachable_with q q': (exists w, reachable_with q w q') <-> q' el reach q.
Proof.
 rewrite <- reachable_with_reachable.  apply reach_correct.
Qed.

Lemma delta_star_reach w q: delta_star q w el (reach q).
Proof.
  apply reach_reachable_with. now exists w.
Qed.

Notation in_lang w := (accept w) (only parsing).

Lemma Sig_reach : (forall w, in_lang w) <-> forall (q: A), q el (reach s) -> F q.
Proof.
  split.
  - intros H q E. rewrite <- reach_reachable_with in E. destruct E as [w R].
   rewrite <- R.  apply (H w).
  - intros H w. apply (H (delta_star s w)). apply delta_star_reach.
Qed.    
  
Global Instance Sig_dec : dec (forall w, in_lang w).
Proof.
  decide( forall q, q el reach s -> F q) as [H | H].
  - left. now apply Sig_reach.
  - right. now rewrite Sig_reach.
Qed.

Definition empty := forall w, ~ in_lang w.

Definition neg_F := DecPred (fun x => ~ (@F A  x)).

Definition complement := DFA s neg_F (@delta_S A).

End Reachability.
Notation in_lang A w := (accept A w) (only parsing).
Section Operations.
Variable  A : dfa.

Lemma complement_correct w: accept (complement A) w <-> ~ (accept A w).
Proof.
  split; auto.
Qed.

Global Instance empty_dec : dec (empty A).
Proof.
  apply (dec_trans (@Sig_dec (complement A))). now setoid_rewrite complement_correct.
Qed.

Lemma empty_reach: empty A <-> forall (q:A), q el (reach s) -> ~ (F q).
Proof.
  split.
  - intros empt q E F . rewrite <- reach_reachable_with in E. destruct E as [w R].
    specialize (empt w). apply empt. unfold accept. now rewrite R.
  - intros H w acc. specialize (H (delta_star s w)). apply H.
    + apply delta_star_reach.
    + exact acc.
Qed.

Instance exists_accept_dec: dec (exists w, accept A w).
Proof.
decide (empty A) as [H | H].
- firstorder.
- left. unfold empty in H.  rewrite empty_reach in H. rewrite DM_notAll in H.
  + destruct H as [q H]. destruct (dec_DM_impl _ _ H) as [H' acc].
     rewrite <- reach_reachable_with in H'. destruct H' as [w R]. exists w.  rewrite <- R in acc. 
    apply dec_DN; auto.     
  + auto.
Qed.

Instance exists_not_accept_dec : dec (exists w, ~ accept A w).
Proof.
  decide (forall w, accept A w) as [H|H].
  - right. firstorder.
  - left. rewrite Sig_reach in H. rewrite DM_notAll in H.
    + destruct H as [q H].  destruct (dec_DM_impl _ _ H) as [H' acc].
       rewrite <- reach_reachable_with in H'. destruct H' as [w R]. exists w.  now rewrite <- R in acc. 
    + auto.
Qed.      
    
Definition Epsilon_autom : dfa.
Proof.
  refine (DFA (inl tt) (DecPred (fun q: unit + unit => if q then True else False)) (fun _ _ => inr tt)).
  intros [[]|[]]; auto.
Defined.


Lemma inr_fix_epsilon w : (@delta_star Epsilon_autom (inr tt) w) = inr tt.
Proof.
  now induction w.
Qed.

Lemma Epsilon_autom_correct w: accept Epsilon_autom w <-> w = nil.
Proof.
  split.
  - cbn. destruct w.
    + reflexivity.
    + cbn. now rewrite inr_fix_epsilon.
  - intros H. subst w. cbn. exact I.
Qed.



Definition predCons (A:dfa) (q: option A + unit) := match q with
                                                        | inl None => False
                                                        | inl (Some q) => F q
                                                        | inr tt => False end.

Definition deltaCons x (A:dfa) (q: option A + unit) y  := match q with
                                     | inl None => if decision (y = x) then inl (Some s) else inr tt
                                     | inl (Some q) => inl (Some (delta_S q y))
                                     | inr tt => inr tt end.

Instance predCons_dec  (A:dfa) (q: option A + unit) : dec (predCons q).
Proof.
  destruct q.
  - destruct o; auto.
  - destruct u; auto.
Qed.


Definition cons (A: dfa) (x:Sig) :=
  DFA (inl None) (DecPred (@predCons A)) (@deltaCons x A).


Lemma inr_fix A' x w : (@delta_star (cons A' x) (inr tt) w) = inr tt.
Proof.
  now induction w.
Qed.    

Lemma cons_correct  (A':dfa) x w : accept A' w <-> accept (cons A' x) (x::w).
Proof.
  cbn in *. deq x. unfold accept. generalize (@s A').  induction w; firstorder.
Qed.


Fixpoint exactW (w: word)  := match w with
                     | nil => Epsilon_autom
                     | x::w' => cons (exactW w') x end.

Lemma exactW_correct w w': accept (exactW w) w' <-> w' = w.
Proof.
  split.
    - revert w'; induction w; intros w';  destruct w'.
   + reflexivity.
   + simpl. apply Epsilon_autom_correct.
   + cbn. tauto.
   + intros H. pose proof (@cons_correct (exactW w) a w') as nc; cbn in *. deq a.     
    dec.
    * subst e. rewrite <- nc in H. f_equal. now apply IHw.
    * unfold predCons in *. now rewrite (@inr_fix (exactW w) _  w') in H.
    - intros []. induction w'.
      + exact I.
      + simpl. now rewrite <- cons_correct.
Qed.
    
Variable A':dfa.


Section Product_automaton.
  Variable op: Prop -> Prop -> Prop.
  Variable op_dec: forall P Q, dec P -> dec Q -> dec (op P Q).
  
  Definition prod_delta: A (x) A' -> Sig -> A (x) A' :=
    fun P x  => match P with (q1,q2) => (delta_S q1 x, delta_S q2 x) end.
Definition prod_pred := (fun P => match P with (q1,q2) => op (@F A q1) (@F A' q2) end).

Global Instance prod_pred_dec P: dec (prod_pred P).
Proof.
  destruct P as [q1 q2]. auto.
Qed.

Definition prod_F  := DecPred prod_pred.

Definition prod := DFA (s,s) prod_F prod_delta.

Lemma prod_delta_star w q1 q2 : @delta_star prod (q1, q2) w = (delta_star q1 w, delta_star q2 w).
Proof.
  revert q1 q2. induction w; now cbn.
Qed.

Lemma prod_correct w: accept prod w <-> op (accept A w) (accept A' w).
Proof.
  cbn. now rewrite prod_delta_star.
Qed.

End Product_automaton.
Arguments prod op {op_dec}.

Definition intersect := prod and.

Lemma intersect_correct w: accept intersect w <-> accept A w /\ accept A' w.
Proof.
  apply prod_correct.
Qed.

Definition U :=  prod or.

Lemma U_correct w: accept U w <-> accept A w \/ accept A' w.
Proof.
  apply prod_correct.
Qed.

Definition diff := prod (fun P Q => P /\ ~ Q).

Lemma diff_correct w : accept diff w <-> accept A w /\ ~ accept A' w.
Proof.
  unfold diff. now rewrite prod_correct.
Qed.

Definition lang_incl := forall w, in_lang A w -> in_lang A' w.

Lemma lang_incl_iff : lang_incl <-> empty diff.
Proof.
  unfold empty. setoid_rewrite diff_correct. split.
  - firstorder.
  - intros H w H'. specialize (H w). destruct (dec_DM_and _ H).
    + tauto.
    + apply dec_DN; auto.
Qed.

End Operations.

Definition lang_equiv A A':= lang_incl A A' /\ lang_incl A' A.

Instance lang_sub_dec A A' : dec (lang_incl A A'). 
Proof.
  decide (empty (diff A A')) as [H|H]; unfold empty in H; setoid_rewrite diff_correct in H.
  - left. intros w acc. specialize (H w). decide (accept A' w); tauto.
  - right. firstorder.
Qed.    

Instance equiv_eq_dec A A': dec (lang_equiv A A').
Proof.
  auto.
Qed.

(** * Nondeterministic finite automata (NFA)*)

Record nfa := NFA {
                  Q :> finType;
                  q0:Q;
                  Q_acc: decPred Q;
                  delta_Q: Q -> Sig -> decPred Q
                }.

Implicit Type B : nfa.
Implicit Type A: dfa.
Fixpoint delta_Q_star B q w: B -> Prop  :=
  match w with
  | nil => fun q' => q' = q
  |x::w' => fun q'' => exists q', delta_Q q x q' /\ delta_Q_star q' w' q''
  end.
Arguments delta_Q_star {B} q w q'.

Instance delta_Q_star_dec B (q q': B) w: dec (delta_Q_star q w q').
Proof.
 revert q. induction w.
  - cbn. auto.
  - intros q. cbn. auto.
Qed.

Lemma delta_Q_star_trans B w w' (q q' q'': B) : delta_Q_star q w q' /\ delta_Q_star q' w' q'' -> delta_Q_star q (w ++ w') q''.
Proof.
  intros [H H']. revert q H. induction w; intros q H.
  - cbn in *. congruence.
  - cbn in *. destruct H as [q_m [D H]]. exists q_m. split.
    + exact D.
    + now apply IHw.
Qed.      
    
Definition n_accept B w := exists (q:B), Q_acc q /\ delta_Q_star q0 w q.

Definition toNFA A := @NFA (S A) s F (fun q x => DecPred (fun q' => delta_S q x = q')).


Lemma toNFA_delta_star_correct A q w q': q' = delta_star q w <-> @delta_Q_star (toNFA A) q w q'.
Proof.
  revert q. induction w.
  - reflexivity.
  - intro q; cbn. rewrite IHw. split.
    +eauto.
    +now intros [q'' [[] H]].   
Qed.

Lemma toNFA_correct A : forall w, accept A w <-> n_accept (toNFA A) w.
Proof.
  intros w. unfold accept, n_accept. split.
  - intros H. exists (delta_star s w). now rewrite <- toNFA_delta_star_correct.
  - intros [q [acc H]]. rewrite <- toNFA_delta_star_correct in H. now subst q.
Qed.

Definition toDFA_F B := fun f: B --> bool => exists q, f q /\ Q_acc q.

Definition toDFA_delta B := fun (f: B --> bool) x => vectorise (fun q => toBool (exists q':B, f q' /\ delta_Q q' x q)).

Lemma toDFA_delta_correct B f x q : toDFA_delta f x q -> exists q':B, f q' /\ delta_Q q' x q.
Proof.
  intros H.   unfold toDFA_delta in H. rewrite apply_vectorise_inverse in H. unfold toBool in H. dec.
  - assumption.
  - contradiction H.
Qed.

Definition onestate B q:= (vectorise (fun q':B => toBool (q' = q) )).

Lemma onestate_correct B q q' : @onestate B q q' <-> q = q'.
Proof.
  unfold onestate. rewrite apply_vectorise_inverse. unfold toBool. dec; cbn.
  - subst q. tauto.
  - split; [>tauto | auto].
Qed.

Definition toDFA B := DFA (onestate q0) (DecPred (@toDFA_F B)) (@toDFA_delta B).

Lemma toDFA_delta_star_correct1 B q w q':
  delta_Q_star q w q' -> forall f: B --> bool, f q -> applyVect (@delta_star (toDFA B) f w) q'.
Proof.
  intros H f F. revert f q F H. induction w; intros f q F H; cbn in *.
   -  now subst q'.
   - destruct H as [q'' [H S]]. eapply IHw; eauto.
      unfold toDFA_delta. rewrite apply_vectorise_inverse. unfold toBool. dec.
     + exact I.
     + apply n. now exists q.
  Qed.

Lemma toDFA_delta_star_correct2 B (f: B --> bool) w q':
  applyVect (@delta_star (toDFA B) f w) q' -> exists q, f q /\ delta_Q_star q w q'.
Proof.
  revert f. induction w.
  - cbn. eauto.
  - intros f. cbn. intros H. specialize (IHw _ H). destruct IHw as [q'' [E E']].
    destruct (toDFA_delta_correct E). firstorder.
Qed.
    
Lemma toDFA_correct B w: n_accept B w <-> accept (toDFA B) w.
Proof.
  cbn. unfold n_accept, toDFA_F. split.
  -  intros [q [acc G]]. exists q; split.
     + apply (toDFA_delta_star_correct1 G). now apply onestate_correct.
     + exact acc.       
  -  intros [q [H acc]]. exists q; split.
     + exact acc.
     + destruct (toDFA_delta_star_correct2 H) as [q' [E D]]. rewrite onestate_correct in E. now subst q'.
Qed.

(** * Concatenation of two regular languages *)

Definition concat_acc_pred B B' := fun (q: B + B') => match q with
                                             | inl q => if decision (Q_acc (@q0 B')) then Q_acc q else False
                                             | inr q => Q_acc q
                                             end.

Instance acc_dec B B' q: dec (@concat_acc_pred B B' q).
Proof.
  destruct q as [q | q].
  - cbn. dec; auto.
  - auto.    
Qed.

Definition concat_acc_decPred B B':= DecPred (@concat_acc_pred B B').

Definition concat_delta B B' (q q': B + B') x:= match q with
                                          | inl q => match q' with
                                                    | inl q' => delta_Q q x q'
                                                    | inr q' => if decision (@Q_acc B q) then delta_Q q0 x q' else False
                                                    end
                                          | inr q => match q' with
                                                    | inl q' => False
                                                    | inr q' => delta_Q q x q'
                                                    end
                                          end.

Instance conact_delta_dec B B' (q: B + B') x q' : dec (concat_delta q q' x).
Proof.
  destruct q, q'.
  - auto.
  - cbn. dec; auto.
  - auto.
  - auto.
Qed.

Definition concat_delta_Q B B':= fun (q: B + B') x => DecPred (fun q' => concat_delta q q' x).

Definition concat B B' := NFA (inl (@q0 B)) (@concat_acc_decPred B B') (@concat_delta_Q B B').


Lemma concat_delta_Q_star_correct1 B B' q q' w: @delta_Q_star (concat B B') (inr q) w (inl q') <-> False.
Proof.
  split; try tauto. revert q; induction w; intro q.
  - congruence.
  - cbn. intros [[q''|q''] H]; firstorder.
Qed.      
    
Lemma concat_delta_Q_star_correct2 B B' q q' w:  @delta_Q_star (concat B B') (inl q) w (inl q') <->   delta_Q_star q w q'.
Proof.
  split; revert q; induction w; intro q; try congruence.
  - intros [[q''|q''] [S H]].
    + exists q''. firstorder.
    + now rewrite concat_delta_Q_star_correct1 in H.
  - intro H. firstorder.
Qed.

Lemma concat_delta_Q_star_correct3 B B' q q' w:  @delta_Q_star (concat B B') (inr q) w (inr q') <->   delta_Q_star q w q'.
Proof.
  split; revert q; induction w; intro q; try congruence.
  - intros [[q''|q''] [S H]].
    + contradiction S. 
    + exists q''. firstorder. 
  - intro H. firstorder.
Qed.

Lemma concat_delta_Q_star_correct4 B B' q q' w:  @delta_Q_star (concat B B') (inl q) w (inr q') <->   exists w' q'', delta_Q_star q w' q'' /\ Q_acc q'' /\ exists w'', w = w' ++ w'' /\ delta_Q_star q0 w'' q' /\ (w'' = nil -> q0 <> q').
Proof.
  split; revert q; induction w; intro q; try congruence.
  -intros [[q''|q''] [S H]].
    + specialize (IHw q'' H). destruct IHw as [w' [q_m [S' [acc [w'' [E [D IHw]]]]]]]. exists (a::w'), q_m. repeat split.
      * cbn. now exists q''.
      * exact acc.             
      * subst w. exists w''. tauto.
     +  exists nil, q. cbn in S. dec; repeat split; try tauto.
         exists (a::w). cbn. repeat split; try congruence.
           exists q''. split.
           *  exact S.
           *  eapply concat_delta_Q_star_correct3. exact H.             
 - intros [w' [_ [_ [_ [w'' [E [D H]]]]]]]. symmetry in E. pose proof ( app_eq_nil _ _ E) as [E1 E2].  subst w'' w'.
   cbn in *. exfalso; now apply H.                       
 - intros [w' [q'' [H [ acc [w'' [E [D S]]]]]]]. cbn. destruct w'.
    + cbn in *. subst q'' w''. destruct D as [q'' [D H]]. exists (inr q''). split.
       * now dec.
       * now apply concat_delta_Q_star_correct3.
    +  cbn in *. inv E. destruct H as [q1 [D' H]].  exists (inl q1).  eauto 10.      
Qed.
 
Lemma concat_correct  B B' w : n_accept (concat B B') w <-> exists w' w'', n_accept B w' /\ n_accept B' w'' /\ w = w' ++ w''.
Proof.
  split.
  - intros acc. destruct acc as [q [acc H]]. destruct q as [q |q].
    + cbn in H. rewrite concat_delta_Q_star_correct2 in H. exists w, nil. rewrite app_nil_r. cbn in acc. dec; firstorder.
    + cbn in H.  rewrite concat_delta_Q_star_correct4 in H.  firstorder.
  -  intros [w' [w'' [[q1 [acc1 D1]] [[q2 [acc2 D2]] eqn]]]]. destruct w''.
     +  rewrite app_nil_r in eqn.  subst w'. exists (inl q1). cbn. dec.
      * now rewrite concat_delta_Q_star_correct2.
      * cbn in D2. subst q2. tauto.
     + subst w. exists (inr q2). split; auto. cbn. rewrite concat_delta_Q_star_correct4.
       exists w', q1. firstorder. exists (e::w''). firstorder. congruence.        
Qed.
(** * Kleene Operator *)

Definition kleene_acc_pred B := fun q => match q with
                                      | None => True
                                      | Some q => @Q_acc B q end.

Instance kleene_acc_dec B (q: option B): dec (kleene_acc_pred q).
Proof.
  unfold kleene_acc_pred. destruct q; auto.
Qed.

Definition kleene_acc_decPred B:= DecPred (@kleene_acc_pred B).

Definition kleene_delta B (q: option B) x q':= match q' with
                                                            | Some q' => match q with
                                                                        | None => delta_Q q0 x q'
                                                                        | Some q => delta_Q q x q' \/ (Q_acc q /\ delta_Q q0 x q')
                                                                        end
                                                            | _ => False end.
Instance kleene_delta_dec B (q q': option B) x : dec (kleene_delta q x q').                                                        Proof.
destruct q, q'; auto.                                                                                                                                     Qed.

Definition kleene_star B := NFA (None) (@kleene_acc_decPred B) (fun (q: option B) x => DecPred (fun q' => kleene_delta q x q')).

Lemma nil_kleene B : n_accept (kleene_star B) nil.
Proof.
  unfold n_accept.  now exists q0.
Qed.

Lemma kleene_delta_ok1 B (q q': B) w: delta_Q_star q w q' -> @delta_Q_star (kleene_star B) (Some q) w (Some q').
Proof.
  revert q. induction w; intros q H.
  - cbn in *. congruence.
  - cbn in *.  firstorder.
Qed.

Lemma kleene_delta_ok2 B q q' x w:
  Q_acc q -> @delta_Q_star (kleene_star B) None (x::w) q' -> @delta_Q_star (kleene_star B) q (x::w) q'.
Proof.
  intros acc H. cbn in *. unfold kleene_acc_pred in acc. destruct q.
  - destruct H as [q'' [D H]]. exists q''. split.
    + unfold kleene_delta. destruct q''.
      * tauto.
      * contradiction D.
    + exact H.
  - exact H.    
Qed.

Lemma kleene_delta_ok_3 B w:  n_accept B w -> n_accept (kleene_star B) w.
  destruct w.
  - intros _. apply nil_kleene.
  -  intros [q [acc H]]. exists (Some q). split.
     + exact acc.
     + destruct H as [q' [H' H]]. exists (Some q'). split.
       * exact H'.
       * now apply kleene_delta_ok1.
Qed.


Lemma kleene_delta_ok_4 B x w q': @delta_Q_star B q0  (x:: w) q' -> @delta_Q_star (kleene_star B) q0 (x::w) (Some q').
Proof.    
  cbn. intros [q [H S]]. exists (Some q). split.
  + exact H.
  + now apply kleene_delta_ok1.
Qed.

Lemma kleene_delta_ok_5 B a w:
  n_accept B a -> n_accept (kleene_star B) w -> n_accept (kleene_star B) (a++ w).
Proof.

    (* If there is a rest (w is not empty), then the last state is the last state after reading w, otherwise it is the last state after reading a. we need to know which one it is because we have to commit to a  final state now *)
  destruct w.
  - rewrite app_nil_r. intros H _. now apply kleene_delta_ok_3.
  -  destruct a.
     + now cbn.       
     + intros [q' [acc' H]] [q [acc H1]]. exists q. split.
       * exact acc.
       * eapply delta_Q_star_trans. split.
         {
           apply kleene_delta_ok_4. exact H.
         }
         {
           now apply kleene_delta_ok2.
         }
Qed.

Lemma kleene_star_correct1 B w: (forall w', w' el w -> n_accept B w') -> n_accept (kleene_star B) (List.concat w).
Proof.
  induction w.
  - cbn. intros _. apply nil_kleene.
  - intros H.
    assert (forall w', w' el w -> n_accept B w') as ass by firstorder. specialize (IHw ass); clear ass.
    cbn. apply kleene_delta_ok_5.
    + now apply H.
    + exact IHw.
Qed.
           
Lemma kleene_delta_ok6  B (q:B) w (q':B) :
  @delta_Q_star (kleene_star B) (Some q) w (Some q') -> @delta_Q_star B q w q' \/ exists w' w'' q'', w = w' ++ w'' /\ Q_acc q'' /\ @delta_Q_star B q w' q'' /\ @delta_Q_star (kleene_star B) None w'' (Some q').
Proof.
  revert q. induction w; intros q H.
  - left. cbn in H. now inv H.
  - destruct H as [q_m [H D]]. destruct q_m; try contradiction H. specialize (IHw _ D). destruct H as [H |acc H].
    + destruct IHw as [IHw | [w' [w'' [q'' [E [acc IHw]]]]]]. 
      *  firstorder.        
      *  right. exists (a::w'), w''. subst w. exists q''.  firstorder.
    + right. exists nil, (a::w), q. cbn. firstorder.      
Qed.

Lemma kleene_delta_ok7 B q  w :
  @delta_Q_star (kleene_star B) q w None <-> q= None /\ w = nil.
Proof.
  split.
  - revert q. induction w; intros q H.
    + cbn in H. now subst q.
    + cbn in H. destruct H as [q' [D H]]. specialize (IHw _ H). destruct IHw as [E E']. subst q' w.
      contradiction D.
  - intros [E E']. now subst q w.
Qed.

(* w must not be empty because kleene_star B accepts nil no matter what B does. *)
Lemma kleene_delta_ok8 B x w:
  n_accept (kleene_star B) (x::w) -> n_accept B (x::w) \/ exists w' w'', w = w' ++ w'' /\ n_accept B (x::w') /\ n_accept (kleene_star B) w''.
Proof.
  intros [q  [acc [q' [H S]]]]. cbn in *. destruct q, q'.
  - pose proof (kleene_delta_ok6 S) as [H'|H']; clear S.
    + left. exists e. firstorder.
    + right. destruct H' as [w' [w'' [q [E [acc' [S S']]]]]]. exists w', w''. firstorder.
  - contradiction H.
  - rewrite kleene_delta_ok7 in S. destruct S as [S _]. discriminate S.
  - contradiction H.
Qed.

Lemma kleene_star_correct2 B w :
  n_accept (kleene_star B) w -> exists w', List.concat w' = w /\  (forall w'', w'' el w' -> n_accept B w'').
Proof.
   intros H. induction w using (@size_induction _ (@length Sig)). destruct w.
-  exists nil. firstorder.
- destruct (kleene_delta_ok8 H) as [H' | H']; clear H.
  + exists [(e::w)]. cbn. rewrite app_nil_r. split.
    * reflexivity.
    * now intros w' [[]|  []].
  + destruct H' as [w' [w'' [E [acc1 acc2]]]].
    assert (|w''| < | e::w|) as L.
    {
      subst w. cbn. rewrite app_length. omega. 
    }
    specialize (H0 w'' L acc2); clear L. destruct H0 as [w1 [E' H]]. exists ((e::w')::w1). split.
    * cbn. rewrite E'. now subst w.
    * intros w2 [[]|H']; auto.
Qed.      
 
Lemma kleene_star_correct B w:  n_accept (kleene_star B) w <-> exists w', List.concat w' = w /\  (forall w'', w'' el w' -> n_accept B w'').
Proof.
  split.
  - apply kleene_star_correct2.
  - intros [w' [[] H]]. now apply kleene_star_correct1.
Qed.
    
End DFA.





      
    
        
                                                             
