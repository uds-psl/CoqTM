Require Import TM.Code.CodeTM.
Require Import TM.LiftMN.
Import Vector.

Open Scope vector_scope.

Ltac getFin i j := apply (Fin.of_nat_lt (ltac:(omega) : i < j)).

Definition bool2nat := fun b : bool => if b then 1 else 0.
Coercion bool2nat : bool >-> nat.
Print Graph.
Compute true  : nat.
Compute false : nat.

Search "swap" Fin.t.

Section Count.
  Variable (X : eqType).

  Definition count (n : nat) (x : X) (xs : t X n) :=
    fold_right (fun y c => if Dec (x = y) then S c else c) xs 0.

  Lemma count0_notIn (n : nat) (x : X) (xs : t X n) :
    count x xs = 0 -> ~ In x xs.
  Proof.
    revert x. induction xs; intros; cbn in *.
    - vector_not_in.
    - intros H1. decide (x=h); try congruence.
      apply In_cons in H1 as [-> | H1]; try tauto.
      eapply IHxs; eauto.
  Qed.

  Lemma count0_notIn' (n : nat) (x : X) (xs : t X n) :
    ~ In x xs -> count x xs = 0.
  Proof.
    induction xs; intros; cbn in *.
    - reflexivity.
    - decide (x = h) as [ -> | D ].
      + contradict H. constructor.
      + apply IHxs. intros H2. contradict H. now constructor.
  Qed.

  Lemma countDupfree (n : nat) (xs : t X n) :
    (forall x : X, In x xs -> count x xs = 1) <-> dupfree xs.
  Proof.
    split; intros H.
    {
      induction xs; cbn -[count] in *.
      - constructor.
      - constructor.
        + intros H2. specialize (H h ltac:(now constructor)). cbn in H.
          decide (h = h); try tauto. inv H.
          contradict H2. now eapply count0_notIn.
        + apply IHxs. intros x Hx. specialize (H x ltac:(now constructor)).
          cbn in H. decide (x = h); inv H; auto. rewrite H1.
          contradict Hx. now eapply count0_notIn.
    }
    {
      Check dupfree_ind.
      induction H as [ | n x' xs HIn HDup IH ]; intros; cbn in *.
      - inv H.
      - decide (x = x') as [ -> | D].
        + f_equal. exact (count0_notIn' HIn).
        + apply (IH x). now apply In_cons in H as [ -> | H].
    }
  Qed.


(* (* Test *)
End Count.
Compute let xs := [|1;2;3;4;5;6|] in
        let x  := 2 in
        let y  := 1 in
        let i  := Fin.F1 in
        Dec (x = y) + count x xs = Dec (x = xs[@i]) + count x (replace xs i y).
*)

  Lemma replace_nth (n : nat) (xs : Vector.t X n) (p : Fin.t n) :
    replace xs p xs[@p] = xs.
  Proof.
    eapply eq_nth_iff. intros ? ? <-.
    decide (p = p1) as [ -> | D].
    - now rewrite Vector_replace_nth.
    - now rewrite Vector_replace_nth2.
  Qed.
  
  Lemma count_replace (n : nat) (xs : t X n) (x y : X) (i : Fin.t n) :
    Dec (x = y) + count x xs = Dec (x = xs[@i]) + count x (replace xs i y).
  Proof.
    induction xs; intros; cbn -[nth count] in *.
    - inv i.
    - dependent destruct i; cbn -[nth count] in *.
      + decide (x = y) as [ D | D ]; cbn -[nth count] in *; cbn -[bool2nat dec2bool count].
        * rewrite <- D in *. decide (x = h) as [ -> | D2]; cbn [dec2bool bool2nat plus]; auto.
          cbv [count]. cbn. rewrite D. decide (y = y); try tauto. decide (y = h); congruence.
        * decide (x = h); subst; cbn [bool2nat dec2bool plus]; cbv [count]; try reflexivity.
          -- cbn. decide (h = h); try tauto. decide (h = y); tauto.
          -- cbn. decide (x = h); try tauto. decide (x = y); tauto.
      + cbn. decide (x = y); cbn.
        * decide (x = h); cbn; f_equal.
          -- decide (x = xs[@p]); cbn; repeat f_equal; subst.
             ++ symmetry. now apply replace_nth.
             ++ cbn in *. specialize (IHxs p). decide (h = xs[@p]); tauto.
          -- decide (x = xs[@p]); cbn; repeat f_equal; subst.
             ++ symmetry. now apply replace_nth.
             ++ cbn in *. specialize (IHxs p). decide (y = xs[@p]); tauto.
        * decide (x = h); cbn; f_equal.
          -- decide (x = xs[@p]); cbn; f_equal; subst.
             ++ cbn in *. specialize (IHxs p). decide (xs[@p] = xs[@p]); cbn in *; try tauto.
             ++ specialize (IHxs p). cbn in *. decide (h = xs[@p]); cbn in *; tauto.
          -- decide (x = xs[@p]); cbn; auto.
             ++ specialize (IHxs p). cbn in *. decide (x = xs[@p]); cbn in *; tauto.
             ++ specialize (IHxs p). cbn in *. decide (x = xs[@p]); cbn in *; tauto.
  Qed.
  
End Count.

Lemma dupfree_nth_injective (X : Type) (n : nat) (xs : Vector.t X n) :
  dupfree xs -> forall (i j : Fin.t n), xs[@i] = xs[@j] -> i = j.
Proof.
  induction 1; intros; cbn -[nth] in *.
  - inv i.
  - dependent destruct i; dependent destruct j; cbn -[nth] in *; auto.
    + cbn in *. contradict H. eapply vect_nth_In; eauto.
    + cbn in *. contradict H. eapply vect_nth_In; eauto.
    + f_equal. now apply IHdupfree.
Qed.

Section Swap.
  Variable (n : nat) (X : Type).
  Variable xs : Vector.t X n.
  Variable (i1 j1 : Fin.t n).

  Definition swap : Vector.t X n :=
    tabulate_vec' (fun i : Fin.t n =>
                     if Dec (i = i1)
                     then xs[@j1]
                     else if Dec (i = j1)
                          then xs[@i1]
                          else xs[@i]).

  Lemma swap_dupfree :
    dupfree xs -> dupfree swap.
  Proof.
    intros H.
    apply dupfree_tabulate_functional. intros x y.
    decide (x = i1) as [D1 | D1]; decide (y = i1) as [D2 | D2];
    decide (x = j1) as [D3 | D3]; decide (y = j1) as [D4 | D4];
    intros H'; subst; try congruence.
    all: try now (eapply dupfree_nth_injective; eauto).
    all: apply dupfree_nth_injective in H'; eauto; congruence.
  Qed. 

  Lemma swap_nth_i1 : swap[@i1] = xs[@j1].
  Proof. unfold swap. rewrite nth_tabulate'. decide (i1 = i1); tauto. Qed.
  Lemma swap_nth_j1 : swap[@j1] = xs[@i1].
  Proof. unfold swap. rewrite nth_tabulate'. decide (j1 = i1) as [-> | D]; auto. decide (j1 = j1); cbn; tauto. Qed.
  Lemma swap_nth i : i <> i1 -> i <> j1 -> swap[@i] = xs[@i].
  Proof. unfold swap. rewrite nth_tabulate'. decide (i = i1) as [-> | D]; try tauto. decide (i = j1); cbn; tauto. Qed.
  
End Swap.

Compute Vector.map (@fin_to_nat _) (swap (tabulate_vec' (fun i : Fin.t 10 => i)) ltac:(getFin 0 10) ltac:(getFin 0 10)).


Section Swap2.
  Variable (n : nat) (X : Type).
  Variable xs : Vector.t X n.
  Variable (i1 i2 : Fin.t n).
  Variable (j1 j2 : Fin.t n).

  Definition swap2 : t X n :=
    tabulate_vec'
      (fun i =>
         if Dec (i = i1) then xs[@j1]
         else if Dec (i = i2) then xs[@j2]
              else if Dec (i = j1) then xs[@i1]
                   else if Dec (i = j2) then xs[@i2]
                        else xs[@i]).

  Hypothesis comp : (i1 = i2 /\ j1 = j2 \/ i1 <> i2 /\ j1 <> j2).

  Lemma swap2_dupfree :
    dupfree xs -> dupfree swap2.
  Proof.
    intros H. unfold swap2. apply dupfree_tabulate_functional. intros x y.
    decide (x = i1); decide (y = i1);
    decide (x = i2); decide (y = i2);
    decide (x = j1); decide (y = j1);
    decide (x = j2); decide (y = j2);
    subst; intros H2; auto.
    all: try now (eapply dupfree_nth_injective; eauto).
    all: apply dupfree_nth_injective in H2; eauto; try congruence.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.


Section ChangeAlphabet1.
  Variable (sig : finType).
  Variable (X Y : finType).
  Hypothesis (enc_X : codable sig X) (enc_Y : codable sig Y).

  (* [ 0, 1, ...,  n-1 ] *)
  Definition id_indexes n := tabulate_vec' (fun i : Fin.t n => i).

  Lemma id_indexes_dupfree n : dupfree (id_indexes n).
  Proof.
    eapply dupfree_tabulate_functional. auto.
  Qed.

  Variable (n : nat).
  Variable (i1 i2 : Fin.t n).
  Variable (j1 j2 : Fin.t n).

                          
                     
                
           
  

  Definition indexes1 : t (Fin.t n) n :=
    if Dec (i1 = i2) then
      (swap (id_indexes _) i1 j1)
    else
      swap (swap (id_indexes _) i1 j1) i2 j2.

  Lemma indexes1_dupfree : dupfree indexes1.
  Proof. unfold indexes1. decide (i1 = i2); repeat apply swap_dupfree; apply id_indexes_dupfree. Qed.

  Variable comp : (i1 = i2 /\ j1 = j2 \/ i1 <> i2 /\ j1 <> j2).

  Lemma id_indexes_nth i : (id_indexes n)[@i] = i.
  Proof. unfold id_indexes. now rewrite nth_tabulate'. Qed.
    
  Lemma indexes1_i1 : indexes1[@i1] = j1.
  Proof.
    unfold indexes1. destruct comp as [(D1&D1') | (D1&D1')].
    - subst. decide (i2 = i2); try tauto. rewrite swap_nth_i1. rewrite id_indexes_nth. auto.
    - decide (i1 = i2) as [D2 | D2].
      + subst. rewrite swap_nth_i1. rewrite id_indexes_nth. auto.
      + decide (i1 = j2) as [D3 | D3].
        * subst. rewrite swap_nth_j1.
          decide (i2 = j1) as [D4 | D4].
          -- subst. rewrite swap_nth_j1. rewrite id_indexes_nth. admit.
          -- rewrite swap_nth; eauto. rewrite id_indexes_nth.  admit.
                                               
        * rewrite swap_nth; eauto. rewrite swap_nth_i1. rewrite id_indexes_nth. auto.
      
      + subst. rewrite swap_nth_j1. rewrite swap_nth_j1. rewrite id_indexes_nth. auto.
      + rewrite swap_nth_i1. rewrite swap_nth_j1. rewrite id_indexes_nth; eauto.

      subst. rewrite swap_nth_i1. rewrite swap_nth_j1. rewrite id_indexes_nth. auto.
    - decide (i1 = j2) as [D2 | D2'].
      + subst. rewrite swap_nth_j1. rewrite swap_nth; eauto.
        decide (i2 = j1) as [D3 | D3].
        * subst. congruence.

        rewrite id_indexes_nth. auto.
      + rewrite swap_nth; eauto. rewrite swap_nth; eauto. rewrite id_indexes_nth. auto.
                                                                                    


    rewrite swap_nth_j1.

(* (* Test *)
End ChangeAlphabet1.
Compute Vector.map (@fin_to_nat _) (indexes1 ltac:(getFin 1 10) ltac:(getFin 9 10) ltac:(getFin 4 10) ltac:(getFin 6 10)).
Compute Vector.map (@fin_to_nat _) (indexes1 ltac:(getFin 1 10) ltac:(getFin 1 10) ltac:(getFin 4 10) ltac:(getFin 4 10)).
*)

  Variable F : finType.
  Variable pM : { M : mTM sig^+ n & states M -> F }.

  Definition ChangeAlphabet1 := Inject pM indexes1.

  Lemma ChangeAlphabet1_Computes (f : X -> Y) :
    pM ⊨ Computes_Rel i1 i2 enc_X enc_Y f ->
    ChangeAlphabet1 ⊨ Computes_Rel j1 j2 enc_X enc_Y f.
  Proof.
    intros H. eapply Realise_monotone.
    {
      eapply Inject_Realise; eauto. eapply indexes1_dupfree.
    }
    {
      hnf. intros tin (yout&tout) (H1&_). hnf in H1. hnf. intros x Hx. specialize (H1 x).
      unfold reorder in H1. erewrite !nth_map in H1; eauto.
    }
    
    
    

End ChangeAlphabet1.

(*
Compute map (@fin_to_nat _) (id_indexes 42).
*)