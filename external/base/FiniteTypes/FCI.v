

(* (** * Finite Closure Iteration *) *)
(* Section Fixedpoints. *)
(*   Variable X: Type. *)
(*   Variable f: X -> X. *)
(*   Definition fp x := f x = x. *)

(*   Lemma fp_trans x: fp x -> fp (f x). *)
(*   Proof. *)
(*     congruence. *)
(*   Qed. *)
  
(*   Lemma fInduction (p: X -> Prop) (x:X) (px: p x) (IHf: forall y, p y -> p (f y)) n: p (Nat.iter n f x). *)
(*   Proof. *)
(*     induction n. *)
(*     - exact px. *)
(*     -  firstorder. *)
(*   Qed. *)

(* Lemma fp_iter_trans x n: fp (Nat.iter n f x) -> forall m, m >= n -> fp (Nat.iter m f x). *)
(* Proof. *)
(*   intros F m H. induction m. *)
(*   - destruct n; auto. omega.  *)
(*   - decide (S m = n). *)
(*     + now rewrite e. *)
(*     + assert (m >= n) as G by omega. *)
(*       specialize (IHm G). simpl. now apply fp_trans. *)
(* Qed. *)

(* End Fixedpoints. *)

(* Definition admissible (X: eqType) f := forall A: list X,  fp f A \/ card (f A) > card A. *)
  

(* Lemma fp_card_admissible (X:eqType) f n: *)
(*   admissible f -> forall A: list X, fp f (Nat.iter n f A) \/ card (Nat.iter n f A) >= n. *)
(*  Proof. *)
(*    intros M A. induction n. *)
(*      - cbn in *. right. omega. *)
(*      - simpl in *. destruct IHn as [IHn | IHn] . *)
(*        + left.  now apply fp_trans. *)
(*        + destruct (M ((Nat.iter n f A))) as [M' | M']. *)
(*          * left.  now apply fp_trans. *)
(*          * right. omega.  *)
(*  Qed. *)

(*  Lemma fp_admissible (X:finType) (f: list X -> list X): *)
(*    admissible f -> forall A, fp f (Nat.iter (Cardinality X) f A). *)
(*  Proof. *)
(*    intros F A. *)
(*    destruct (fp_card_admissible (Cardinality X) F A) as [H | H]. *)
(*    - exact H. *)
(*    - specialize (F (Nat.iter (Cardinality X) f A)).  destruct F as [F |F]. *)
(*      + tauto. *)
(*      + pose proof (card_upper_bound (f (Nat.iter (Cardinality X) f A))). omega. *)
(* Qed.  *)

(* Section FiniteClosureIteration. *)
(*   Variable X : finType. *)
(*   Variable step:list X -> X -> Prop. *)
(*   Variable step_dec: forall A x, dec (step A x). *)

  
(*   Lemma pick A : {x | step A x /\ ~ (x el A)} + forall x, step A x -> x el A. *)
(*   Proof. *)
(*     decide (forall x, step A x -> x el A). *)
(*     - tauto. *)
(*     - left. destruct (DM_notAll _ (p:= fun x => step A x -> x el A)) as [H _]. *)
(*       destruct (finType_cc _ (H n)) as [x H']. firstorder. *)
(*   Defined. *)

(*   Definition FCStep A := *)
(*     match (pick A) with *)
(*     | inl L => match L with *)
(*                 exist _ x _ => x::A end *)
(*     | inr _ => A end. *)

(*   Definition FCIter := Nat.iter (Cardinality X) FCStep. *)

(* Lemma FCStep_admissible: admissible FCStep. *)
(* Proof. *)
(*   intro A.  unfold fp. unfold FCStep. destruct (pick A) as [[y [S ne]] | S];auto. *)
(*   right. cbn. dec. *)
(*   - tauto. *)
(*   - omega. *)
(* Qed. *)

(* Lemma FCIter_fp A: fp FCStep (FCIter A). *)
(* Proof. *)
(*   unfold FCIter. apply fp_admissible. exact FCStep_admissible. *)
(* Qed.         *)

(* (* inclp A p means every x in A satisfies p *) *)

(* Lemma FCIter_ind (p: X -> Prop) A :  inclp A p ->  (forall A x , (inclp A p) -> (step A x -> p x)) -> inclp (FCIter A) p. *)
(* Proof. *)
(*   intros incl H. unfold FCIter. apply fInduction. *)
(*   - assumption.  *)
(*   - intros B H1 x E. unfold FCStep in E. destruct (pick B) as [[y [S nE]] | S]. *)
(*     + destruct E as [E|E]; try subst x; eauto. *)
(*     + auto. *)
(* Qed.  *)

(* Lemma Closure x A: fp FCStep A -> step A x -> x el A. *)
(* Proof. *)
(*   intros F. unfold fp in F.  unfold FCStep in F. destruct (pick A) as [[y _] | S]. *)
(*   - contradiction (list_cycle F). *)
(*   - exact (S x). *)
(* Qed. *)

(* Lemma Closure_FCIter x A: step (FCIter A) x -> x el (FCIter A). *)
(* Proof. apply Closure. apply FCIter_fp. *)
(* Qed. *)

(* Lemma preservation_step A: A <<= FCStep A. *)
(* Proof. *)
(*   intro H. unfold FCStep. destruct (pick A) as [[y [S ne]] | S]; cbn; tauto. *)
(* Qed. *)

(* Lemma preservation_iter A n: A <<= Nat.iter n FCStep A. *)
(* Proof. *)
(*   intros x E. induction n. *)
(*   - assumption. *)
(*   - simpl. now apply preservation_step. *)
(* Qed. *)

(* Lemma preservation_FCIter A: A <<= FCIter A.  *)
(* Proof. *)
(*  apply preservation_iter. *)
(* Qed. *)

(* Definition least_fp_containing f (B A: list X) := fp f B /\ A <<= B /\ forall B', fp f B' /\ A <<= B' -> B <<= B'. *)

(* Definition step_consistent:= forall A x, step A x -> forall A', A <<= A' -> step A' x. *)

(* Lemma step_iter_consistent: step_consistent -> forall A x n, step A x -> step (Nat.iter n FCStep A) x. *)
(* Proof. *)
(*   intros H A x n S. eapply H. *)
(*   - exact S. *)
(*   - apply preservation_iter. *)
(* Qed. *)



(* Lemma step_trans_fp_incl: step_consistent -> forall A B, fp FCStep B -> A <<= B -> forall n, Nat.iter n FCStep A <<= B. *)
(* Proof. *)
(*  intros ST A B F H n. apply fInduction. *)
(*   - exact H. *)
(*   - intros B' H'. unfold FCStep at 1. destruct (pick B') as [[y [S _]] | _]. *)
(*     + specialize (ST  _ _ S _ H'). intros x [E |E]. *)
(*       * subst x. now apply Closure. *)
(*       * auto. *)
(*     + exact H'. *)
(* Qed. *)

(* Lemma step_consistent_least_fp: step_consistent -> forall A, least_fp_containing FCStep (FCIter A) A. *)
(* Proof. *)
(*   intros ST A.  repeat split. *)
(*   - apply FCIter_fp. *)
(*   - apply preservation_FCIter. *)
(*   - intros B [H H']. now apply step_trans_fp_incl. *)
(* Qed. *)

(*   (** Dupfreeness of FCIter *)
(* - relict of an old proof *)
(* - might still be useful in concrete applications *) *)

(* Lemma dupfree_FCStep A: dupfree A -> dupfree (FCStep A). *)
(* Proof. *)
(*   intro DA. unfold FCStep. destruct (pick A) as [[y [S ne]] | S]; auto. now constructor. *)
(* Qed. *)

(*  Lemma dupfree_iterstep n A: dupfree A -> dupfree (Nat.iter n FCStep A). *)
(*  Proof. *)
(*    induction n. *)
(*    -  now cbn. *)
(*    - intro H. simpl. apply dupfree_FCStep; tauto. *)
(*  Qed. *)

(*  Lemma dupfree_FCIter A : dupfree A -> dupfree (FCIter A). *)
(*  Proof. *)
(*    apply dupfree_iterstep. *)
(*  Qed. *)

(* End FiniteClosureIteration. *)
(* Arguments FCIter {X} step {step_dec} x. *)
(* Arguments FCStep {X} step {step_dec} A. *)
(* Arguments pick {X} {step} {step_dec} A. *)


      
