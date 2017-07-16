Require Import TM Shared.FiniteTypes Nop If TM.Combinators.Combinators Basic.Basic Basic.Mono Basic.Multi.

Hint Rewrite
     runion_restrict
     function_restrict
     compose_id
     rif_restrict
     rcomp_restrict
     rintersect_restrict
     rif_restrict
     ignoreParam_restrict
  : rels.

Smpl Create lift_proper.

(* Smpl Add (eapply subrel_eqrel_proper           ) : lift_proper. *)
Smpl Add (eapply eqrel_rcomp_proper            ) : lift_proper.
Smpl Add (eapply eqrel_star_proper             ) : lift_proper.
Smpl Add (eapply eqrel_union_proper            ) : lift_proper.
Smpl Add 200 (match goal with [ |- rintersection _ _ =2 _ ] => eapply eqrel_rintersection_proper end) : lift_proper.
Smpl Add (eapply eqrel_lift_proper             ) : lift_proper.
Smpl Add (eapply eqrel_plift_proper            ) : lift_proper.
Smpl Add (eapply eqrel_restrict_proper         ) : lift_proper.
Smpl Add (eapply eqrel_rif_proper              ) : lift_proper.
Smpl Add (eapply eqrel_rprod_proper            ) : lift_proper.
Smpl Add (eapply eqrel_ignoreParam_proper      ) : lift_proper.
Smpl Add (eapply eqrel_hideParam_proper        ) : lift_proper.
Smpl Add (match goal with [ |- ⇑[ _] _ =2 _ ] => reflexivity | [ |- _ = _ ] => reflexivity end) : lift_proper.
(* Smpl Add (eapply functionalOn_eqrel_proper     ) : lift_proper. *)
(* Smpl Add (eapply eqrel_lift_gen_proper         ) : lift_proper. *)
(* Smpl Add (eapply eqrel_lift_gen_p_proper       ) : lift_proper. *)
(* Smpl Add (eapply eqrel_lift_gen_eq_proper      ) : lift_proper. *)
(* Smpl Add (eapply eqrel_lift_gen_eq_p_proper    ) : lift_proper. *)
Smpl Add (eapply finite_rel_union_proper       ) : lift_proper.
Smpl Add (eapply rifb_proper                   ) : lift_proper.
Smpl Add 250 (reflexivity) : lift_proper.
Smpl Create rewrite_lift.

Smpl Create reflexivities.
Smpl Add 99 (reflexivity) : reflexivities.
Ltac reflexivity_fun :=
    match goal with
    | [ |- ?L =2 ?R ?x ] =>
      let HH := fresh "HH" in
      let H := fresh "H" in

      pose (HH := L);
      assert (H : L = (fun x => HH) x) by reflexivity;
      pattern x in HH;
      rewrite H;
      subst HH;
      reflexivity
    end.
Smpl Add (reflexivity_fun) : reflexivities.

Ltac autorewrite_lift' :=
  (* TODO: try a "try intros" here *)
  (try match goal with [ |- context [ pointwise_relation ] ] => let x := fresh "x" in intros x; cbn in x end);
  etransitivity; [ smpl lift_proper; autorewrite_lift' | (symmetry; smpl rewrite_lift ) || smpl reflexivities ].

Ltac autorewrite_lift :=
  match goal with
  | [ |- _ <<=2 _ ] => eapply subrel_eqrel_proper; [ symmetry; autorewrite_lift' | reflexivity | ]
  | [ |- functionalOn _ _ ] => eapply functionalOn_eqrel_proper
  end.
Tactic Notation "autorewrite" "lift" := autorewrite_lift.

Smpl Add (eapply restrict_vector_lift_eq) : rewrite_lift.
Smpl Add (eapply restrict_vector_lift_eq) : rewrite_lift.
Smpl Add (eapply star_vector_lift_eq) : rewrite_lift.
Smpl Add (eapply ignoreParam_vector_lift_eq) : rewrite_lift.
Smpl Add (eapply compose_vector_lift_eq2) : rewrite_lift.
Smpl Add (eapply runion_vector_lift_eq) : rewrite_lift.
Smpl Add (match goal with [ |- _ =2 rintersection _ _ ] => eapply rintersect_vector_lift_eq end) : rewrite_lift.
Smpl Add (eapply runion_vector_lift_eq2) : rewrite_lift.
Smpl Add (eapply rintersect_vector_lift_eq2) : rewrite_lift.
Smpl Add (eapply id_vector_lift) : rewrite_lift.
Smpl Add (eapply compose_vector_lift_eq) : rewrite_lift.
Smpl Add (eapply compose_vector_lift_eq2) : rewrite_lift.
Smpl Add (eapply function_vector_lift_eq) : rewrite_lift.

Smpl Create solve_shelved.

Lemma of_nat_inj n ni nj (i : ni < n) (j : nj < n) :
  Fin.of_nat_lt i = Fin.of_nat_lt j -> ni = nj.
Proof.
  (* revert j. induction ni. *)
  (* - destruct n; intros; try omega. *)
  (*   subst. destruct nj. reflexivity. *)
  (*   cbn in H. inv H. *)
  (* - intros. cbn in *. destruct n. *)
  (*   + cbn in *. omega. *)
  (*   + destruct nj.  *)
  (*     * inv H. *)
  (*     * inv H. f_equal.  *)
Admitted.

Smpl Add (
  match goal with
        [ |- permute _ _ = _ ] => now (cbn; dec; [ exfalso; eauto using of_nat_inj | reflexivity | congruence ])
      | [ |- permute _ _ = _ ] => now (cbn; dec; tauto)
      | [ |- _ <> _ ] => congruence
      | [ |- _ ] => now eassumption
          end)  : solve_shelved.

Ltac solve_shelved := smpl solve_shelved.

Smpl Create rewrite_lift_gen.


Ltac autorewrite_lift_gen' :=
  (* TODO: try a "try intros" here *)
  (try match goal with [ |- context [ pointwise_relation ] ] => let x := fresh "x" in intros x; cbn in x end);
  etransitivity; [ smpl lift_proper; autorewrite_lift_gen' | smpl rewrite_lift_genA || smpl reflexivities ].

Ltac autorewrite_lift_gen :=
  match goal with
  | [ |- _ <<=2 _ ] => eapply subrel_eqrel_proper; [ symmetry; autorewrite_lift_gen' | reflexivity | ]
  | [ |- functionalOn _ _ ] => eapply functionalOn_eqrel_proper
  end.

Tactic Notation "autorewrite" "lift_gen" := autorewrite_lift_gen. (* try (setoid_rewrite <- id_lift_gen_eq); repeat smpl rewrite_lift_gen;try solve_shelved. *)

Smpl Create rewrite_lift_genA.


Lemma function_id_lift_gen_eq  X Y n m (I : Vector.t (Fin.t m) n) c :
      (lift_gen_eq_p (X := X) I (↑ (fun y : Y => y = c) ⊗ (@IdR _))) =2 (↑ (fun y : Y => y = c) ⊗ (@IdR _)).
Proof.
  setoid_rewrite <- id_lift_gen_eq at 2.
  now setoid_rewrite <- function_lift_gen_eq.
Qed.

Smpl Add (symmetry; eapply restrict_lift_gen_eq)    : rewrite_lift_genA.
Smpl Add (eapply function_lift_gen_eq)    : rewrite_lift_genA.
Smpl Add (symmetry; eapply function_id_lift_gen_eq)    : rewrite_lift_genA.
Smpl Add (symmetry; eapply compose_lift_gen_eq2)    : rewrite_lift_genA.
Smpl Add (symmetry; eapply runion_lift_gen_eq2)     : rewrite_lift_genA.
Smpl Add (symmetry; eapply ignoreParam_lift_gen_eq) : rewrite_lift_genA.
Smpl Add (symmetry; eapply star_lift_gen_eq)        : rewrite_lift_genA.
Smpl Add (symmetry; eapply runion_lift_gen_eq)        : rewrite_lift_genA.

Smpl Add (setoid_rewrite <- restrict_lift_gen_eq) : rewrite_lift_gen.
Smpl Add (setoid_rewrite <- restrict_lift_gen_eq) : rewrite_lift_gen.
Smpl Add (setoid_rewrite <- function_lift_gen_eq) : rewrite_lift_gen.
Smpl Add (setoid_rewrite <- compose_lift_gen_eq2) : rewrite_lift_gen.
Smpl Add (setoid_rewrite <- runion_lift_gen_eq2) : rewrite_lift_gen.
Smpl Add (setoid_rewrite <- ignoreParam_lift_gen_eq) : rewrite_lift_gen.
Smpl Add (setoid_rewrite <- star_lift_gen_eq) : rewrite_lift_gen.

Ltac TMcrush' :=
  cbn in *; unfold IdR; subst;
  try (now congruence);
  try (now eassumption);
  match goal with
  | [ H : ?P |- context [Dec ?P] ] => decide P; [ | tauto]
  | [ H : ?P |- context [Decb ?P]] => decide P; [ | tauto]
  | [ H : Decb ?P = true |- _ ] => assert P by firstorder; subst; clear H
  | [ H : IdR _ _ |- _] => unfold IdR in H; subst
  | [ |- context[ Vector.nth ?t (Fin.of_nat_lt ?pos) ] ] =>
    change (Vector.nth t (Fin.of_nat_lt pos)) with (get_at pos t)
  | [ H: context[ Vector.nth ?t (Fin.of_nat_lt ?pos)] |- _ ]  =>
    change (Vector.nth t (Fin.of_nat_lt pos)) with (get_at pos t) in H
  | [ H : current ?V = Some _   |- _ ] => let E := fresh "E" in destruct V eqn:E; inv H
  | [ H : Some _ = current ?V   |- _ ] => symmetry in H
  | [ H : get_at ?pos ?t = _ |- context[ get_at ?pos ?t ] ] => rewrite H
  | [ |- exists c, Some c = Some ?e /\ _] => exists e; intuition
  | [ |- exists c, Some ?e = Some c /\ _] => exists e; intuition
  | [ |- Vector.cons _ _ _ _ = Vector.cons _ _ _ _ ] => f_equal
  | [ H : Eq_in (fun y : nat => y = project ?i_is_a_tape -> False) ?t ?x |- context[get_at ?j_is_a_tape ?t] ] => (rewrite H; [ |now eauto])
  | [ H : Eq_in (fun y : nat => y <> project ?i_is_a_tape) ?t ?x |- context[get_at ?j_is_a_tape ?t] ] => 
    (rewrite H; [ |now eauto])
  | [ H : Eq_in (fun y : nat => y = project ?i_is_a_tape -> False) ?x ?t |- context[get_at ?j_is_a_tape ?t] ] =>
    (rewrite <- H; [ |now eauto]; lock H)
  | [ H : Eq_in (fun y : nat => y <> project ?i_is_a_tape) ?x ?t |- context[get_at ?j_is_a_tape ?t] ] => 
    (rewrite <- H; [ |now eauto]; lock H)
  | [ |- Eq_in (not_indices _) _ _] => etransitivity; ( eapply Eq_in_not_indices; [  | eauto | ]; eauto; cbn; rewrite !Fin.to_nat_of_nat; repeat econstructor )
  | [ H : midtape _ _ _ = midtape _ _ _ |- _] => inv H
  | [ H : leftof _ _ = leftof _ _ |- _ ] => inv H
  | [ H : rightof _ _ = rightof _ _ |- _] => inv H
  | [ H : current ?t = None, H2 : ?t = midtape _ _ _ |- _] => rewrite H2 in H; inv H
  | [ H : None = current ?t |- _ ] => symmetry in H
  | [ H : get_at ?i ?t = _, H2 : context[ right (get_at ?i ?t) ] |- _ ] => rewrite H in H2
  | [ |- Eq_in ?P ?v (Vector.replace _ _ _) ] => eapply Eq_in_replace; [
                                                 unfold not_indices;cbn;
                                                 rewrite !Fin.to_nat_of_nat;
                                                 intros V; eapply V; repeat econstructor | ]
  | [ |- Eq_in _ ?v ?v ] => reflexivity
  | [ |- Eq_in _ _ _ ] => now etransitivity; eauto
  | [ H : ?b = _ |- context[if ?b then _ else _] ] => rewrite H
 (* etransitivity; ( *)
                                     (*   eapply Eq_in_not_indices) *)(* ; [ eauto | | cbn; rewrite !Fin.to_nat_of_nat ]; [ | | ]; eauto ) *)
  (* | [ H : Eq_in (fun y : nat => y <> ?tape_i ) ?t ?x |- context[get_at ?j_is_a_tape ?t] ] =>  *)
  (*   let H' := fresh "H" in *)
  (*   assert (H' : tape_i <> project j_is_a_tape) by (unfold project; eauto); rewrite H; eauto; try clear H' *)
  (* | [ H : Eq_in (fun y : nat => y <> ?tape_i) ?x ?t |- context[get_at ?j_is_a_tape ?t] ] => *)
  (*   let H' := fresh "H" in *)
  (*   assert (H' : tape_i <> project j_is_a_tape) by (unfold project; eauto); rewrite <- H; eauto; try clear H' *)
  (* | [ H : Eq_in (fun y : nat => y = ?tape_i -> False) ?x ?t |- context[get_at ?j_is_a_tape ?t] ] =>  *)
  (*   let H' := fresh "H" in *)
  (*   assert (H' : tape_i <> project j_is_a_tape) by (unfold project; eauto); rewrite <- H; eauto; try clear H' *)
  end; cbn.

Ltac TMcrush := (repeat TMcrush'); unlock all.

(* TACTICDEF *)

Smpl Create TMstep.

Ltac TMstep := smpl TMstep.

Smpl Add (match goal with
               (* | [ |- forall _ : eqType_X (type (finType_CS)), _ ] => intros f; repeat destruct f *)
               | [ |- le _ _] => cbn; econstructor
               | [ |- le _ _] => cbn; omega
                                      
               | [ |- RealiseIn (existT _ (projT1 (If _ _ _ _)) _) _ _] => eapply If_total
               | [ |- RealiseIn (existT _ (Match _ _) _) _ _] => eapply If_total
               | [ |- RealiseIn (existT _ (Match _ _) _) _ _] => eapply Match_total
               | [ |- RealiseIn (existT _ (projT1 (Seq _ _)) _) _ _ ] => eapply RealiseIn_changeP; [ eapply Seq_total | intros s; repeat destruct s; firstorder ]
               | [ |- RealiseIn (existT _ (projT1 _) _) _ _] =>
                 eapply RealiseIn_changeP; [ eapply Nop_total | intros s; repeat destruct s; firstorder]

               | [ |- WRealise (existT _ ?x _) _ ] => unfold x
               | [ |- WRealise (existT _ (?x _) _) _ ] => unfold x
               | [ |- WRealise (existT _ (?x _ _) _) _ ] => unfold x
               | [ |- WRealise (existT _ (While _ _) _) _ ] => eapply While_sem
               | [ |- WRealise (existT _ (projT1 (If _ _ _ _)) _) _ ] => eapply If_sem
               | [ |- WRealise (existT _ (Match _ _) _) _ ] => eapply Match_sem

               | [ |- terminatesIn (While _ _) _] =>  eapply While_terminatesIn
               | [ |- terminatesIn ?x _] => unfold x
               | [ |- terminatesIn (?x _) _] => unfold x
               | [ |- terminatesIn (projT1 (If _ _ _ _)) _ ] => eapply If_terminatesIn
               | [ |- terminatesIn (projT1 (MATCH _ _ _)) _ ] => eapply Match_terminatesIn
               end) : TMstep.

Smpl Add 101 (match goal with
              | [ |- RealiseIn _ _ _ ] => exact _
              | [ |- RealiseIn _ _ _ ] => now eauto
              | [ |- RealiseIn _ _ _ ] => eapply RealiseIn_monotone

              | [ |- WRealise _ _ ] => eapply Realise_total; now TMstep
              | [ |- WRealise _ _ ] => eapply WRealise_monotone

              | [ |- terminatesIn _ _] => eapply Realise_total
              end) : TMstep.

Smpl Create TMrel.

Smpl Add (match goal with
      | [ |- subrel _ (_ (Some _)) ] =>  intros ? ? H; eapply lift_option_subrel; eauto; exact H
      | [ |- subrel _ (lift_option _ _ _) ] => cbn; reflexivity
      | [ |- context [finite_rel_union _] ] => assert True by tauto
      | [ |- _ <<=2 _ ] => intros ? ? ? * ?; intros; eassumption
      end) : TMrel.

Ltac TMrel := smpl TMrel.

Tactic Notation "finally" tactic(t1) tactic(t2) :=
  t1; [t2] || t1.

Ltac do_whatever := assert True by tauto.
Ltac undo_whatever := repeat match goal with [ H : True |- _ ] => clear H end. 

Smpl Create shelve_all.

Ltac shelve_all := smpl shelve_all; undo_whatever.

Smpl Add (match goal with
  | [ |- context[WRealise] ] => do_whatever
  | [ |- context[RealiseIn]] => do_whatever
  | [ |- context[subrel]] => do_whatever
  | [ |- context[liftT]] => do_whatever
  | [ |- context[liftT_gen]] => do_whatever
  | [ |- context[functionalOn]] => do_whatever
  | [ |- context[terminatesIn]] => do_whatever
          end) : shelve_all.

Smpl Add 1000 shelve : shelve_all.

Ltac TMcorrect :=
  (finally (repeat TMstep; try TMrel)
          (match goal with
           | [ |- subrel _ _ ] =>
             match goal with
             | [ |- context[ lift_gen ] ] => autorewrite lift_gen
             | [ |- context[ lift_gen_p ] ] => autorewrite lift_gen
             | [ |- context[ lift_gen_eq ] ] => autorewrite lift_gen
             | [ |- context[ lift_gen_eq_p ] ] => autorewrite lift_gen
             end ||  autorewrite lift
           end);
  try match goal with
      | [ |- subrel (lift_gen_eq_p _ _) (lift_gen_eq_p _ _) ] => eapply lift_gen_eq_p_subrel
      | [ |- subrel _ _ ] => eapply vector_lift_eq_subrel
      end);    
  repeat match goal with [ H : True |- _ ] => clear H end; shelve_all.

Existing Class RealiseIn.
Existing Instance Parmove_step_sem.
Existing Instance Nop_total.

Hint Extern 0 (_ <> _) => eassumption : typeclass_instances.

Ltac TMnormaliseH1 := repeat
                        match goal with
                        | [ x : unit * _ |- _ ] => destruct x as ([] & ?)
                        | [ H : Rsnd1 _ _ |- _ ] => inv H
                        | [ H : rcomp _ _ _ _  |- _ ] => destruct H
                        | [ H : _ /\ _ |- _ ] => destruct H
                        | [ H : rintersection _ _ _ _ |- _ ] => destruct H
                        | [ H : restrict _ _ _ _ |- _ ] => destruct H
                        | [ H : lift_vector_rel _ _ _ _ |- _] => cbn in H
                        | [ H : lift_vector_prel _ _ _ _ |- _ ] => cbn in H
                        | [ H : ignoreParam _ _ _ |- _ ] => cbn in H
                        | [ H : rprod _ _ _ _ |- _ ] => destruct H
                        | [ H : IdR _ _ |- _ ] => unfold IdR in H; subst
                        | [ H : ignoreFirst _ _ _ |- _ ] => cbv in H; subst
                        | [ H : exists _, _ |- _ ] => destruct H
                        end.
Ltac TMnormaliseH2 :=
  match goal with
  | [ H : runion _ _ _ _ |- _ ] => destruct H
  | [ H : _ \/ _ |- _ ] => destruct H
  end.

Ltac TMnormaliseH := locked firstorder; (repeat (TMnormaliseH1; TMnormaliseH2)); TMnormaliseH1.

Ltac TMnormaliseG :=
  unfold runion;
  repeat match goal with
         | [ |-  _ /\ _ ] => split
         | [ |- rintersection _ _ _ _] => split
         | [ |- lift_gen_eq _ _ _ _ ] => split
         | [ |- lift_gen_eq_p _ _ _ _ ] => split
         | [ |- if ?b then _ else _ ] => destruct b; TMnormaliseH
         | [ |- rif _ _ _ ?y ] => destruct y; cbn in *; TMnormaliseH
         | [ |- context [Dec (?x = ?x)] ] => decide (x = x); [ subst | tauto]
         | [ |- context [Dec (?x <> ?x)] ] => decide (x <> x); [ tauto | ]
         | [ H : ~ ?x <> ?x |- _ ] => clear H
         | [ H : ?x = ?x |- _ ] => clear H
         end.

Ltac TMnormalise := TMnormaliseH; TMnormaliseG.

(** * Total machines *)

(** ** Copy one symbol *)   

Section copy_char.

  Variable sig : finType.
  Variable tapes_no : nat.

  Variable tape_i : nat.
  Hypothesis i_is_a_tape : tape_i < S tapes_no.

  Variable tape_j : nat.
  Hypothesis j_is_a_tape : tape_j < S tapes_no.

  Hypothesis neq : tape_i <> tape_j.

  Definition Copy_char := MATCH (Read_char sig i_is_a_tape)
                  (fun s : option sig => match s with
                                        None =>  Nop tapes_no sig false
                                      | Some s => Write (sig := sig) j_is_a_tape s ;; Nop tapes_no sig true
                                      end).

  Definition Copy_char_R := if? (fun t t' : tapes sig 2 => exists c, current (get_at tape_0 t) = Some c /\
                                          get_at tape_1 t' = midtape (left (get_at tape_1 t)) c (right (get_at tape_1 t)) /\
                                          get_at tape_0 t' = get_at tape_0 t)
                                ! (fun t t' => current (get_at tape_0 t) = None) ∩ (@IdR _).

  Lemma idlift_lift_eq (X Y : Type) (ni n : nat) (i : ni < n) (c : Y) :
    ⇑[ i] (↑ (fun y : Y => y = c) ⊗ (@IdR X)) =2 ↑ (fun y : Y => y = c) ⊗ (@IdR _).
  Proof.
    rewrite <- id_vector_lift.
    rewrite <- function_vector_lift_eq.
    reflexivity.
  Qed.
  
  Lemma Copy_char_sem :
    Copy_char ⊨(4) ⇑⇑[i_is_a_tape; j_is_a_tape] Copy_char_R.
  Proof.
    Existing Instance read_char_sem.
    Existing Instance write_sem.

    TMcorrect.
    repeat destruct f;TMcorrect.
    
    intros t (b & t') H.
    eapply finite_rel_union_spec in H. cbn in *.
    unfold Copy_char_R.
    destruct H as ([] & ?); cbn in *;
    repeat (TMnormalise; TMcrush).
  Qed.

End copy_char.

(** ** Compare one symbol *)   
    
Section compare_char.
  
  Variable sig : finType.
  Variable tapes_no : nat.

  Variable tape_i : nat.
  Hypothesis i_is_a_tape : tape_i < S tapes_no.

  Variable tape_j : nat.
  Hypothesis j_is_a_tape : tape_j < S tapes_no.

  Hypothesis neq : tape_i <> tape_j.

  Definition Compare_char :=
    MATCH (Read_char sig i_is_a_tape)
          (fun s => match s with
                   None =>  (Nop tapes_no sig false)
                 | Some s =>  (Test_chr j_is_a_tape (fun x => Decb (x = s)))
                 end).
  
  Definition Compare_char_R :=
    if? (fun t t' => exists c, current (sig := sig) (get_at tape_0 t) = Some c /\ current (get_at tape_1 t) = Some c) ∩ (@IdR _)
        ! (fun t t' =>
           (exists c c', current (get_at tape_0 t) = Some c /\
                       current (get_at tape_1 t) = Some c' /\
                       c <> c') \/
           current (get_at tape_0 t) = None \/
           current (get_at tape_1 t) = None) ∩ (@IdR _).
    
  Lemma Compare_char_sem :
    Compare_char ⊨(3) ⇑⇑[i_is_a_tape; j_is_a_tape] Compare_char_R.
  Proof.
    Existing Instances read_char_sem test_chr_sem.
    TMcorrect.
    repeat destruct f;TMcorrect.
    
    intros t (b & t') H.
    eapply finite_rel_union_spec in H. cbn in *.
    unfold Compare_char_R.
    destruct H as ([] & ?); cbn in *; split; try ( firstorder ); cbn in *.
    + TMnormalise; intuition TMcrush.
      eauto 8.
    + TMnormalise. TMcrush.
    + TMnormalise; intuition TMcrush. 
    + TMnormalise; intuition TMcrush.
  Qed.

End compare_char.

(** * Complex but total machines including while *)

(** ** Move to the end of a tape *)

Section move_to_end.
  
  Variable tapes_no : nat.
  Variable sig : finType.
  
  Variable on_tape : nat.
  Hypothesis is_a_tape : on_tape < S tapes_no.

  Definition move_to_end D := While (projT1 (Move sig is_a_tape D)) (projT2 (Move sig is_a_tape D)).

  Definition R_move_to_end_r :=
     (ignoreParam (Y := unit)
                              (((fun t t' => current t = None) ∩ (@IdR _)) ∪ (fun t t' => (forall c ls rs, t = midtape ls c rs -> t' = mk_tape (sig := sig) (rev rs ++ c :: ls) None [])))).
    
  Lemma move_to_end_r_sem :
    move_to_end R ⊫(fun _ => tt) ⇑[is_a_tape] R_move_to_end_r.
  Proof.
    Existing Instance move_sem.
    TMcorrect.

    intros ? ([] & ?) (t' & Hloop & Hterm & Eq).
    unfold lift_vector_rel, IdR, rintersection, runion in *.
    cbn in *. subst.
    induction Hloop.
    - firstorder.
    - firstorder; subst.
      + right. destruct rs; firstorder subst. firstorder. inv H1.
      + right. firstorder subst.
        destruct rs; cbn in *.
        * inv H0. inv Hloop. eauto.
          cbn in *. firstorder congruence.
        * replace ((rev rs ++ [e]) ++ c :: ls) with (rev rs ++ e :: (c :: ls)); eauto.
          now autorewrite with list.
  Qed.

  Lemma move_to_end_r_term :
    move_to_end R ↓ liftT is_a_tape (fun x i => i >= 2 * |right x| + (match current x with None => 0 | Some _ => 2 end) + 1).
  Proof.
    TMcorrect.
    - unfold MoveR.
      eapply functionalOn_lift.
      hnf.
      intros ? ? ? ([ | ] & ? ) ([ | ] & ?) ? ?; firstorder congruence.
    - cbn in *. intros. unfold liftT in H. intuition.
      destruct (get_at is_a_tape x) eqn:E.
      + cbn in *. exists x, false, i. firstorder. now rewrite E.
      + cbn in *. exists x, false, i. firstorder. now rewrite E.
      + cbn in *. exists x, false, i. firstorder. now rewrite E.
      + exists (tape_move_multi x (do_on_tape is_a_tape (None, TM.R))). exists true. exists 1. { split. split.
        * simpl_TM. now rewrite E.
        * simpl_TM.
        * intuition.
          eexists. split. econstructor.
          simpl_TM. rewrite E in *.
          cbn in *. destruct _; cbn in *; omega. }
    Qed.
    
End move_to_end.

(** ** Move to a certain symbol (defined by a predicate) *)

Section move_to_symbol.
  
  Variable tapes_no : nat.
  Variable sig : finType.
  
  Variable on_tape : nat.
  Hypothesis is_a_tape : on_tape < S tapes_no.

  Variable f : sig -> bool.

  Definition M1 D := If (Test_chr is_a_tape f) (Nop tapes_no sig false) (Move sig is_a_tape D).

  Definition R1 D :=
    (if? (fun t t' => exists c, current t = Some c /\ f c = false) ∩ (fun t t' => t' = tape_move_mono t (None,D))
       ! ((@IdR _) ∩ ((fun t _ => current t = None) ∪ (fun t _ => exists c, current t = Some c /\ f c = true)))).

  Lemma M1_sem D : M1 D ⊨(3) (⇑[is_a_tape] (R1 D)).
  Proof.
    Existing Instance test_chr_sem.
    Existing Instance move_sem.
    
    TMcorrect.
    unfold R1. cbn.
    autorewrite with rels.
    intros ? ? H. destruct y. destruct b.
    - cbn in *. destruct H. TMnormalise; TMcrush.
      TMnormalise; TMcrush.
    - cbn in *. destruct H; TMnormalise; intuition TMcrush.
    Qed.
    
  Definition move_to_symbol D := WHILE (M1 D).
  
  Fixpoint to_symbol_list_l l1 l2 {struct l2} :=
    match (l2,l1) with
    | ([],[]) => niltape _
    | ([], c :: l) => leftof c l
    | (c :: l, l1) => if f c then midtape l c l1 else to_symbol_list_l (c :: l1) l
    end.

  (* Careful: if the cursor is left of the tape, nothing will happen! *)
  Fixpoint to_symbol_l t :=
    match t with
    | niltape _ => niltape _
    | leftof c r => leftof c r
    | rightof c r => rightof c r
    | midtape l1 c l2 => to_symbol_list_l l2 (c :: l1)
    end.
  
  Definition R_move_to_symbol_l := ⇑[is_a_tape] (ignoreParam (Y := unit) (fun t t' =>
                                                                            (t' = to_symbol_l t))).

  Fixpoint to_symbol_list l1 l2 :=
    match (l2,l1) with
    | ([],[]) => niltape _
    | ([], c :: l) => rightof c l
    | (c :: l, l1) => if f c then midtape l1 c l else to_symbol_list (c :: l1) l
    end.

  (* Careful: if the cursor is left of the tape, nothing will happen! *)
  Fixpoint to_symbol_r t :=
    match t with
    | niltape _ => niltape _
    | leftof c r => leftof c r
    | rightof c r => rightof c r
    | midtape l1 c l2 => to_symbol_list l1 (c :: l2)
    end.
  
  Definition R_move_to_symbol_r := ⇑[is_a_tape] (ignoreParam (Y := unit) (fun t t' =>
                                  (t' = to_symbol_r t))).
    
  Lemma move_to_symbol_r_sem :
    move_to_symbol R ⊫ R_move_to_symbol_r.
  Proof.
    Existing Instance M1_sem.
    TMcorrect.

    unfold R1.
    autorewrite with rels.
    
    cbn.
    intros ? ([] & ?) (t' & Hloop & Hterm).
    cbn in *. induction Hloop.
    - TMnormalise. 
      + destruct t; try reflexivity. inv H0.
      + TMcrush. 
    - TMnormalise. 
      + firstorder TMcrush. now destruct _. 
      + TMcrush. destruct l2; cbn in *; firstorder congruence.
  Qed.

  Fixpoint time_symbol_list l1 l2 :=
    match (l2,l1) with
    | ([],[]) => 1
    | ([], c :: l) => 1
    | (c :: l, l1) => 1 + if f c then 0 else 1 + time_symbol_list (c :: l1) l
    end.

  Fixpoint time_until_symbol t :=
    match t with
    | niltape _ => 1
    | leftof c r => 1
    | rightof c r => 1
    | midtape l1 c l2 => time_symbol_list l1 (c :: l2)
    end.
  
  Lemma move_to_symbol_r_term :
    projT1 (move_to_symbol R) ↓ liftT is_a_tape (fun x i => i >= 3 * time_until_symbol x).
  Proof.
    cbn -[M1].
    TMcorrect.
    - unfold MoveR.
      eapply functionalOn_lift.
      hnf.
      intros ? ? ? ([] & ? ) ([] & ?) ? ?; firstorder congruence.
    - intros. intuition. unfold liftT in H.
      destruct (get_at is_a_tape x) eqn:E.
      + cbn in *. exists x, false, i. firstorder. left. rewrite E. firstorder. 
      + cbn in *. exists x, false, i. firstorder. left. rewrite E. firstorder. 
      + cbn in *. exists x, false, i. firstorder. left. rewrite E. firstorder. 
      + cbn in *. destruct (f e) eqn:E2.
        * exists x, false, i. firstorder. right. rewrite E. firstorder. 
        * exists (tape_move_multi x (do_on_tape is_a_tape (None, TM.R))). exists true. exists 3.
        { split. split.
          * simpl_TM. now rewrite E. 
          * intuition. simpl_TM.
          * simpl_TM.
            unfold liftT.
            rewrite !get_at_tape_move_multi.
            simpl_TM.
            rewrite !E. simpl_TM. cbn. instantiate (1 := 0). cbn.
            destruct l0; cbn in *; omega. 
        }
  Qed.
    
End move_to_symbol.

(** ** Compare two tapes until the end *)

Section compare_tapes.

  Variable sig : finType.
  Variable tapes_no : nat.

  Variable tape_i : nat.
  Hypothesis i_is_a_tape : tape_i < S tapes_no.

  Variable tape_j : nat.
  Hypothesis j_is_a_tape : tape_j < S tapes_no.

  Hypothesis neq : tape_i <> tape_j.

  Definition Compare_tapes_body := If (Compare_char sig i_is_a_tape j_is_a_tape) 
                                      (Parmove_step sig i_is_a_tape j_is_a_tape R)
                                      (Nop tapes_no sig false).

  Definition Compare_tapes_body_R := if?
                      (fun t t' => exists c : sig,
                          current (get_at tape_0 t) = Some c /\
                          current (get_at tape_1 t) = Some c /\
                          get_at tape_0 t' = tape_move_right (get_at tape_0 t) /\
                          get_at tape_1 t' = tape_move_right (get_at tape_1 t)) !
                      (fun t t' => (exists c c', current (get_at tape_0 t) = Some c /\
                                         current (get_at tape_1 t) = Some c' /\
                                         c <> c') \/
                                current (get_at tape_0 t) = None \/
                                current (get_at tape_1 t) = None) ∩ (@IdR _).
                                       
  Lemma Compare_tapes_body_sem :
    Compare_tapes_body ⊨(5) ⇑⇑[i_is_a_tape;j_is_a_tape] Compare_tapes_body_R.
  Proof.
    Existing Instance Compare_char_sem.
    TMcorrect.
    unfold Compare_char_R, Parmove_step_R, Compare_tapes_body_R.
    autorewrite with rels. cbn.

    intros ? ? ?.
    TMnormalise; TMcrush; eauto 9.
  Qed.
    
  Definition Compare_tapes := While (projT1 Compare_tapes_body) (projT2 Compare_tapes_body).

  Definition mk_rtape (ls rs : list sig) :=
    match rs with
    | c :: rs => midtape ls c rs
    | nil => match ls with
            | List.nil => niltape _
            | l :: ls => rightof l ls
            end
    end.
  
  Definition Compare_tapes_R :=
  (fun (t t' : tapes sig _) => exists ls0 ls1 pre rs0 rs1,
         get_at tape_0 t = mk_rtape ls0 (pre ++ rs0) /\
         get_at tape_1 t = mk_rtape ls1 (pre ++ rs1) /\
         get_at tape_0 t' = mk_rtape (rev pre ++ ls0) rs0 /\
         get_at tape_1 t' = mk_rtape (rev pre ++ ls1) rs1 /\
         match rs0, rs1 with
           x :: _, y :: _ => x <> y
         |  _,_ => True
         end) ∪ (fun t t' => (current (get_at tape_0 t) = None \/ current (get_at tape_1 t) = None) /\ t = t').
  
  Lemma Compare_tapes_sem :
    Compare_tapes ⊫(fun _ => tt) ⇑⇑[i_is_a_tape; j_is_a_tape] ignoreParam (Compare_tapes_R).
  Proof.
    Hint Resolve Compare_tapes_body_sem.
    repeat TMstep; try TMrel.
    
    TMcorrect.

    unfold Compare_tapes_R, Compare_tapes_body_R.
    autorewrite with rels.
    intros ? ([] & ?) ?; cbn in *.
    
    destruct H. destruct H. destruct H0. TMcrush.
    unfold runion in *.
    induction H.
    - cbn in *. TMnormalise; try tauto.
      TMcrush. 
      left.
      eexists _, _, [], (x0 :: _), (x1 :: _). cbn.
        autorewrite with list; eauto. 
    -  
      decompose [ex and or] H; clear H.
      eapply IHstar in H0.
      left. clear IHstar. clear H1.
      TMcrush. clear E E0.
      exists l1, l.
      decompose [or and] H0; subst.
      + clear H0. firstorder. cbn in *.
        destruct *; TMcrush.
        all:(destruct x1, x2, x3; TMcrush).
        all:(try destruct x4; TMcrush).
        all:(try destruct x5; TMcrush).
        all:(rewrite H in H4; inv H4).
        all:(rewrite H0 in H6; inv H6).
        all:(try now eexists [x0], _, _; firstorder).
        all:(eexists (x0 :: _ :: x3), _, _; firstorder;
                 cbn in *; now autorewrite with list).
      + cbn in H4. destruct l2, (get_at tape_0 z); inv H; inv H4.
        eexists [x0], [], _.
        destruct l0; cbn; firstorder. cbn. firstorder.
      + destruct l0, (get_at tape_1 z); inv H; inv H6.
        eexists [x0], _, []. firstorder.
        now destruct l2.
  Qed.
  
  Fixpoint compare_tapes_time_list (r1 r2 : list sig) :=
    6 +
    match r1, r2 with
    | x1 :: r1, x2 :: r2 => if Dec (x1 = x2)
                           then compare_tapes_time_list r1 r2
                           else 0
    | _, _ => 0
    end.                                                 

  Definition compare_tapes_time (t t' : tape sig) :=
    match t, t' with
      midtape l1 x1 r1, midtape l2 x2 r2 => compare_tapes_time_list  (x1 :: r1) (x2 :: r2)
    | _, _ => 6
    end.
  
  Lemma compare_tapes_term :
    Compare_tapes ↓ liftT_gen [| Fin.of_nat_lt i_is_a_tape; Fin.of_nat_lt j_is_a_tape |]%vector_scope
                  (fun x i =>
                     i >= compare_tapes_time (get_at tape_0 x) (get_at tape_1 x)).
  Proof.
    Hint Resolve Compare_tapes_body_sem.
    TMcorrect.
    - unfold Compare_tapes_body_R. cbn.
      eapply functionalOn_lift_gen.
      hnf.
      intros ? ? ? ([ | ] & ? ) ([ | ] & ?) ? ?.
      cbn in *. f_equal;
      eapply get_at_eq_iff; intros [ |[ | ]]; firstorder; try omega;
        erewrite get_at_ext; rewrite ?H3, ?H4; symmetry; erewrite get_at_ext; rewrite ?H6, ?H7; reflexivity.
      cbn in *. firstorder congruence.
      cbn in *. firstorder congruence.
      
      cbn in *. f_equal. firstorder; TMcrush.
    - cbn in *. intros. unfold liftT_gen in H. intuition.
      unfold compare_tapes_time in H.
      cbn in *.
      destruct (x[@i_is_a_tape]) eqn:E;  destruct (x[@j_is_a_tape]) eqn:E2.
      all:(try now  exists x, false, i; firstorder; cbn in *; rewrite E, E2; firstorder).
      decide (e = e0).
      + exists (tape_move_multi x (do_on_tapes tape_i tape_j (None, TM.R))). exists true. exists 5. { split. split.
        * simpl_TM. now rewrite E. cbn. rewrite E2. subst. reflexivity.
        * simpl_TM. 
        * intuition.
          eexists. split. econstructor. 
          simpl_TM. subst. rewrite E in *.
          cbn in *. destruct _; cbn in *. omega. destruct l2.
          rewrite E2. cbn in *. omega. rewrite E2. cbn in *. omega. }
      + exists x, false, i; firstorder; cbn in *; rewrite E, E2; firstorder.
  Qed.
      
End compare_tapes.

(** ** Compare two tapes until a certain marker symbol is reached *)

Section compare_tapes_until.

  Variable sig : finType.
  Variable tapes_no : nat.

  Variable tape_i : nat.
  Hypothesis i_is_a_tape : tape_i < S tapes_no.

  Variable tape_j : nat.
  Hypothesis j_is_a_tape : tape_j < S tapes_no.

  Hypothesis neq : tape_i <> tape_j.

  Variable until : sig -> bool.
  
  Definition Compare_tapes_until_body := If (Test_chr i_is_a_tape until)
                                            (Nop tapes_no sig false)
                                            (Compare_tapes_body sig i_is_a_tape j_is_a_tape ).

  Definition Compare_tapes_until_body_R := if?
                      (fun t t' => exists c : sig,
                          current (get_at tape_0 t) = Some c /\
                          current (get_at tape_1 t) = Some c /\
                          until c = false /\
                          get_at tape_0 t' = tape_move_right (get_at tape_0 t) /\
                          get_at tape_1 t' = tape_move_right (get_at tape_1 t)) !
                      (fun t t' => (exists c c', current (get_at tape_0 t) = Some c /\
                                         current (get_at tape_1 t) = Some c' /\
                                         c <> c') \/
                                (exists c, current (get_at tape_0 t) = Some c /\ until c = true) \/
                                current (get_at tape_0 t) = None \/
                                current (get_at tape_1 t) = None) ∩ (@IdR _).
                                       
  Lemma Compare_tapes_until_body_sem :
    Compare_tapes_until_body ⊨(7) ⇑⇑[i_is_a_tape;j_is_a_tape] Compare_tapes_until_body_R.
  Proof.
    Existing Instances test_chr_sem Compare_tapes_body_sem.
    TMcorrect.
    unfold Compare_char_R, Parmove_step_R, Compare_tapes_body_R, Compare_tapes_until_body_R.
    rewrite function_lift_gen_eq. rewrite id_lift_gen_eq.
    autorewrite with rels. cbn.

    intros ? ([] & ?) ?; TMnormalise; cbn; try now TMcrush.
    all:try(etransitivity; TMcrush).
    - TMnormalise; cbn; intuition TMcrush. 
    - TMnormalise; cbn. intuition TMcrush. unfold IdR.
      TMcrush'. TMcrush'. TMcrush'. TMcrush'.
      rewrite H, H3; eauto.
    - TMnormalise. cbn. intuition TMcrush.  unfold IdR.
      TMcrush'. TMcrush'. TMcrush'. TMcrush'.
      rewrite H, H3; eauto.
    - TMnormalise. cbn. left. exists x2, x3. TMnormalise; TMcrush.
      TMcrush'. TMcrush'. TMcrush'. TMcrush'.
      rewrite H, H3; eauto.
    - TMnormalise. cbn in *. right. right. right. TMcrush'.
      rewrite H3; TMcrush. unfold project. eauto. cbn in H2.
      TMcrush'. TMcrush'. TMcrush'. TMcrush'.
      rewrite H, H3; eauto.
      Grab Existential Variables. econstructor.
  Qed.
    
  Definition Compare_tapes_until := While (projT1 Compare_tapes_until_body) (projT2 Compare_tapes_until_body).

  Definition compare_list_until := fix compare_list_until (cp : list sig) := fun ls1 ls2 rs => 
    match cp, rs with
    | x :: xs, r :: rs => if Dec (x <> r) then (midtape ls1 x xs, midtape ls2 r rs) else
                           if until x then (midtape ls1 x xs, midtape ls2 r rs)
                           else compare_list_until xs (x :: ls1) ( r :: ls2) rs
    | x :: xs, [] => (midtape ls1 x xs, mk_tape ls2 None [])
    | [], r :: rs => (mk_tape ls1 None [], midtape ls2 r rs)
    | [],[] => (mk_tape ls1 None [], mk_tape ls2 None [])
    end.

  Definition compare_until (t1 t2 : tape sig) : tape sig * tape sig :=
    match t1,t2 with
    | midtape ls c rs, midtape ls' c' rs' => compare_list_until (c :: rs) ls ls' (c' :: rs')
    | _, _ => (t1, t2)
    end.
  
  Definition Compare_tapes_until_R :=
  (fun (t t' : tapes sig _) => (get_at tape_0 t', get_at tape_1 t') = compare_until (get_at tape_0 t) (get_at tape_1 t)).
  
  Lemma Compare_tapes_until_sem :
    Compare_tapes_until ⊫(fun _ => tt) ⇑⇑[i_is_a_tape; j_is_a_tape] ignoreParam (Compare_tapes_until_R).
  Proof.
    Hint Resolve Compare_tapes_until_body_sem.
    TMcorrect.

    unfold Compare_tapes_until_R, Compare_tapes_until_body_R.
    autorewrite with rels.
    intros ? ([] & ?) ?; cbn in *.

    TMnormaliseH1.
    
    induction H.
    - TMnormalise.
      + TMcrush.
      + TMcrush.        
        destruct (get_at tape_1 x) eqn:?; TMcrush.
        decide _; TMcrush.
      + destruct (get_at tape_0 x) eqn:?;
        destruct (get_at tape_1 x) eqn:?; TMcrush.
      + destruct (get_at tape_0 x) eqn:?;
        destruct (get_at tape_1 x) eqn:?; TMcrush.
    - repeat (TMnormalise; TMcrush); destruct *; rewrite H5, H6 in H2; inv H2; TMcrush.
  Qed.
  
  Fixpoint compare_tapes_until_time_list (r1 r2 : list sig) :=
    8 +
    match r1, r2 with
    | x1 :: r1, x2 :: r2 => if Dec (x1 = x2)
                           then if until x1 then 0 else compare_tapes_until_time_list r1 r2
                           else 0
    | _, _ => 0
    end.
                                                 

  Definition compare_tapes_until_time (t t' : tape sig) :=
    match t, t' with
      midtape l1 x1 r1, midtape l2 x2 r2 => compare_tapes_until_time_list  (x1 :: r1) (x2 :: r2)
    | _, _ => 8
    end.
  
  Lemma compare_tapes_until_term :
    Compare_tapes_until ↓ liftT_gen [| Fin.of_nat_lt i_is_a_tape; Fin.of_nat_lt j_is_a_tape |]%vector_scope
                  (fun x i =>
                     i >= compare_tapes_until_time (get_at tape_0 x) (get_at tape_1 x)).
  Proof.
    Hint Resolve Compare_tapes_until_body_sem.
    TMcorrect.
    - unfold Compare_tapes_until_body_R. cbn.
      eapply functionalOn_lift_gen.
      hnf.
      intros ? ? ? ([ | ] & ? ) ([ | ] & ?) ? ?.
      + cbn in *; f_equal; eapply get_at_eq_iff; intros [ |[ | ]]; firstorder; try omega;
           erewrite get_at_ext; rewrite ?H5, ?H4; symmetry; erewrite get_at_ext; rewrite ?H8, ?H9; reflexivity.

      + cbn in *. firstorder congruence.
      + cbn in *. firstorder congruence.
      
      + cbn in *. f_equal. firstorder; TMcrush.
    - cbn in *. intros. unfold liftT_gen in H. intuition.
      unfold compare_tapes_time in H.
      cbn in *.
      destruct (x[@i_is_a_tape]) eqn:E;  destruct (x[@j_is_a_tape]) eqn:E2.
      all:(try now  exists x, false, i; firstorder; cbn in *; rewrite E, E2; firstorder).
      decide (e = e0).
      + destruct (until e) eqn:Ee.
        * exists x, false, i; firstorder; cbn in *. TMcrush. right. left. firstorder. omega.
        * exists (tape_move_multi x (do_on_tapes tape_i tape_j (None, TM.R))). exists true. exists 7. { split. split.
          * simpl_TM. now rewrite E. cbn. rewrite E2. subst. reflexivity.
          * simpl_TM. 
          * intuition.
            eexists. split. econstructor. 
            simpl_TM. subst. rewrite E in *.
            cbn in *. destruct _; cbn in *. decide (e0 = e0); try tauto. rewrite Ee in H.
            omega. destruct l2.
            rewrite E2. cbn in *.
            all:decide (e0 = e0); try tauto; rewrite Ee in H.
            omega. rewrite E2. cbn in *. omega. }
      + exists x, false, i; firstorder; cbn in *. rewrite E, E2; firstorder.
        all:decide (e0 = e0); try tauto;destruct (until e); omega.
  Qed.
      
End compare_tapes_until.

Section copy_tape.

  Variable sig : finType.
  Variable tapes_no : nat.

  Variable tape_i : nat.
  Hypothesis i_is_a_tape : tape_i < S tapes_no.

  Variable tape_j : nat.
  Hypothesis j_is_a_tape : tape_j < S tapes_no.

  Hypothesis neq : tape_i <> tape_j.

  Definition Copy_tapes_body := If (Copy_char sig i_is_a_tape j_is_a_tape)
                                   (Parmove_step sig i_is_a_tape j_is_a_tape R)
                                   (Nop tapes_no sig false).

  Definition Copy_tapes_body_R := if?
                      (fun t t' => exists c : sig,
                          current (get_at tape_0 t) = Some c /\
                          get_at tape_1 t' = tape_move_right (midtape (left (get_at tape_1 t)) c (right (get_at tape_1 t))) /\
                          get_at tape_0 t' = tape_move_right (get_at tape_0 t)) !
                      (fun t t' =>  current (get_at tape_0 t) = None) ∩ (@IdR _).

  Lemma Copy_tapes_body_sem :
    Copy_tapes_body ⊨(6) ⇑⇑[i_is_a_tape;j_is_a_tape] Copy_tapes_body_R.
  Proof.
    Existing Instance Copy_char_sem.
    repeat TMstep; try TMrel.
    TMcorrect.
    unfold Copy_char_R, Parmove_step_R, Copy_tapes_body_R.
    autorewrite with rels. cbn.
    
    intros ? ? ?. 
    destruct y as ([] & ?);firstorder; TMcrush. 
  Qed.
    
  Definition Copy_tapes := While (projT1 Copy_tapes_body) (projT2 Copy_tapes_body).

  Definition copy_list := fix copy_list (cp : list sig) := fun ls rs => 
    match cp, rs with
    | x :: xs, _ :: rs => copy_list xs ( x :: ls) rs
    | x :: xs, [] => copy_list xs (x :: ls) rs 
    | [], r :: rs => midtape ls r rs
    | [],[] => match ls with [] => niltape _ | l :: ls => rightof  l ls end
    end.

  Definition copy (t1 t2 : tape sig) : tape sig :=
    match t1,t2 with
    | midtape ls c rs, midtape ls' c' rs' => copy_list (c :: rs) ls' (c' :: rs')
    | midtape ls c rs, leftof a bs => copy_list rs [c] (a :: bs)
    | midtape ls c rs, rightof a bs => copy_list (c :: rs) (a :: bs) []
    | midtape ls c rs, niltape _ => copy_list (c :: rs) [] []
    | _, _ => t2 
    end.
  
  Definition Copy_tapes_R :=
  (fun (t t' : tapes sig _) => get_at tape_1 t' = copy (get_at tape_0 t) (get_at tape_1 t))
    ∩ ((fun t t' => (current (get_at tape_0 t) = None) /\ t = t')
         ∪ (fun t t' => (exists c ls rs, get_at tape_0 t = midtape ls c rs /\ get_at tape_0 t' = mk_tape (sig := sig) (rev rs ++ c :: ls) None []))).                                                              

  Lemma Copy_tapes_sem :
    Copy_tapes ⊫(fun _ => tt) ⇑⇑[i_is_a_tape; j_is_a_tape] ignoreParam (Copy_tapes_R).
  Proof.
    Existing Instance Copy_tapes_body_sem.
    TMcorrect.
    unfold Copy_tapes_R, Copy_tapes_body_R.
    autorewrite with rels.
    intros ? ([] & ?) ?; cbn in *.
    
    destruct H. destruct H. destruct H0. TMcrush.
    unfold runion, rintersection in *.
    induction H.
    - cbn in *. firstorder.
      destruct get_at; inv H0; reflexivity.
    - TMnormalise; TMcrush.
      + subst. destruct (get_at tape_1 x); cbn in *; TMcrush.
        all:(destruct l0; cbn in *; TMcrush).
      + destruct (get_at tape_1 x); cbn in *; TMcrush.
        all:(destruct l0; cbn in *; TMcrush); right.
        all:(repeat eexists; firstorder).
      +  destruct (get_at tape_1 x); cbn in *; TMcrush.
         all:(destruct l0; cbn in *; TMcrush).
         destruct l2; TMcrush.
      + right.
        all:(repeat eexists; firstorder).
        rewrite H5 in H3.
        destruct l0; inv H3. cbn.
        autorewrite with list. reflexivity.
  Qed.
  
  Lemma Copy_tapes_term :
    Copy_tapes ↓ liftT_gen [|Fin.of_nat_lt i_is_a_tape; Fin.of_nat_lt j_is_a_tape|]%vector_scope
                  (fun x i =>
                     i >= 7 + (|right (get_at tape_0 x)| +
                         match current (get_at tape_0 x) with Some _ => 1 | _ => 0 end) * 7).
  Proof.
    TMcorrect.
    - unfold Copy_tapes_body_R. cbn -[mult].
      eapply functionalOn_lift_gen.
      hnf.
      intros ? ? ? ([ | ] & ? ) ([ | ] & ?) ? ?; firstorder; TMcrush.
      cbn in *. f_equal.
      
      eapply get_at_eq_iff; intros [ | [ | ]]; firstorder; try omega.
      + erewrite get_at_ext; rewrite ?H3, ?H2; symmetry; erewrite get_at_ext; rewrite ?H6, ?H4; eauto.
      +  erewrite get_at_ext; rewrite ?H3, ?H2; symmetry; erewrite get_at_ext; rewrite ?H6, ?H4; eauto. now inv H0.
    - cbn in *. intros. unfold liftT_gen in H. cbn in *.
      destruct (x[@i_is_a_tape]) eqn:E. cbn in *.
      all:(try now  exists x, false, i; firstorder; cbn in *; rewrite E; firstorder).
      pose (t0 := tape_move_right x[@i_is_a_tape]).
      pose (t1 := tape_move_right (midtape (left x[@j_is_a_tape]) e (right x[@j_is_a_tape]))).
      exists (Vector.replace (Vector.replace x j_is_a_tape t1) i_is_a_tape t0).
      exists true. exists 6. intuition; eauto.
      + unfold lift_gen_eq_p, lift_gen_p, runion, rintersection.
        cbn -[tape_move_right t0]. split.
        rewrite E. exists e. firstorder.
        * unfold get_at. rewrite Vector_replace_nth2.
         rewrite Vector_replace_nth. unfold t1. TMcrush. 
         intros L; eapply neq.
         assert (Fin.to_nat i_is_a_tape = Fin.to_nat j_is_a_tape) by congruence.
         rewrite !Fin.to_nat_of_nat in H0. congruence.
        * unfold get_at. rewrite Vector_replace_nth. unfold t0. TMcrush.
        * TMcrush.
      + simpl_TM. unfold liftT_gen. cbn.
        rewrite mult_comm in *. cbn in *.
        rewrite Vector_replace_nth. subst t0. subst t1.
        cbn in *. TMcrush. destruct _; cbn in *; omega. 
  Qed.
      
End copy_tape.

Section copy_tape_until.

  Variable sig : finType.
  Variable tapes_no : nat.

  Variable tape_i : nat.
  Hypothesis i_is_a_tape : tape_i < S tapes_no.

  Variable tape_j : nat.
  Hypothesis j_is_a_tape : tape_j < S tapes_no.

  Hypothesis neq : tape_i <> tape_j.

  Variable until : sig -> bool.

  Definition Copy_tapes_until_body := If (Test_chr i_is_a_tape until)
                                         (Nop tapes_no sig false)
                                         (Copy_tapes_body sig i_is_a_tape j_is_a_tape).

  Definition Copy_tapes_until_body_R :=
    if?
        (fun t t' => exists c : sig,
             current (get_at tape_0 t) = Some c /\
             until c = false /\
             get_at tape_1 t' = tape_move_right (midtape (left (get_at tape_1 t)) c (right (get_at tape_1 t))) /\
             get_at tape_0 t' = tape_move_right (get_at tape_0 t)) !
      ((fun t t' =>  current (get_at tape_0 t) = None) ∪ (fun t t' => exists c, current (get_at tape_0 t) = Some c /\ until c = true)) ∩ (@IdR _).

      
   
  Lemma Copy_tapes_until_body_sem :
    Copy_tapes_until_body ⊨(8) ⇑⇑[i_is_a_tape;j_is_a_tape] Copy_tapes_until_body_R.
  Proof.
    Existing Instances test_chr_sem Copy_tapes_body_sem.
    TMcorrect.
    - unfold tapes.

      rewrite <- !lift_gen_eq_p_singleton.
      rewrite <- !restrict_lift_gen_eq.
      rewrite <- !compose_lift_gen_eq2.

      rewrite lift_gen_eq_extend, lift_gen_eq_p_extend; eauto.
      
      setoid_rewrite <- compose_lift_gen_eq2.
      rewrite <- !runion_lift_gen_eq2.
      eapply lift_gen_eq_p_subrel.

      autorewrite with rels. cbn.

      intros ? ? ?. 
      destruct y as ([ | ] & ?); firstorder; TMcrush.
      + eapply get_at_eq_iff; intros [ | [ | ]]; firstorder; try omega.
        erewrite get_at_ext; rewrite ?H0, ?H; symmetry; erewrite get_at_ext; rewrite ?H0, ?H, ?E; eauto.
      + eapply get_at_eq_iff; intros [ | [ | ]]; firstorder; try omega.
  Qed.
    
  Definition Copy_tapes_until := While (projT1 Copy_tapes_until_body) (projT2 Copy_tapes_until_body).
  
  Definition copy_list_until := fix copy_list (cp : list sig) := fun ls rs => 
    match cp, rs with
    | x :: xs, r :: rs => if until x then midtape ls r rs  else copy_list xs ( x :: ls) rs
    | x :: xs, [] => if until x then match ls with [] => niltape _ | l :: ls => rightof  l ls end else copy_list xs (x :: ls) rs 
    | [], r :: rs => midtape ls r rs
    | [],[] => match ls with [] => niltape _ | l :: ls => rightof  l ls end
    end.

  Definition copy_until (t1 t2 : tape sig) : tape sig :=
    match t1,t2 with
    | midtape ls c rs, midtape ls' c' rs' => copy_list_until (c :: rs) ls' (c' :: rs')
    | midtape ls c rs, leftof a bs => if until c then t2 else copy_list_until rs [c] (a :: bs)
    | midtape ls c rs, rightof a bs => copy_list_until (c :: rs) (a :: bs) []
    | midtape ls c rs, niltape _ => copy_list_until (c :: rs) [] []
    | _, _ => t2
    end.
  
  Definition Copy_tapes_until_R :=
  (fun (t t' : tapes sig _) => get_at tape_1 t' = copy_until (get_at tape_0 t) (get_at tape_1 t))
    ∩ ((fun t t' => (current (get_at tape_0 t) = None) /\ t = t')
         ∪ (fun t t' => (exists c ls rs, get_at tape_0 t = midtape ls c rs /\ get_at tape_0 t' = to_symbol_r until (get_at tape_0 t)))).

  Lemma Copy_tapes_until_sem :
    Copy_tapes_until ⊫(fun _ => tt) ⇑⇑[i_is_a_tape; j_is_a_tape] ignoreParam (Copy_tapes_until_R).
  Proof.
    Existing Instance Copy_tapes_until_body_sem.
    TMcorrect.
    unfold Copy_tapes_until_R, Copy_tapes_until_body_R.
    autorewrite with rels.
    intros ? ([] & ?) ?; cbn in *.
    
    destruct H. destruct H. destruct H0. TMcrush.
    unfold runion, rintersection in *.
    induction H.
    - cbn in *. firstorder.
      + destruct get_at; inv H; reflexivity.
      + TMcrush. destruct _; reflexivity.
      + TMcrush. eauto 9.
    - destruct H. destruct H. destruct H2. destruct H3.
      destruct IHstar; eauto.
      TMcrush. firstorder.
      + subst. TMcrush. destruct (get_at tape_1 x); cbn in *; TMcrush.
        all:(destruct l0; cbn in *; TMcrush).
      + destruct (get_at tape_1 x); cbn in *; TMcrush.
      + TMcrush.
        destruct l0; cbn; destruct (get_at tape_1 x) eqn:?; try destruct l2; reflexivity.
      + TMcrush.
        destruct l0; cbn; try reflexivity.
        * destruct (get_at tape_1 x) eqn:?; try reflexivity.
        * destruct (get_at tape_1 x) eqn:?; try destruct l4; try reflexivity.
      + TMcrush. right.
        repeat econstructor. destruct l0; try reflexivity.
        cbn. destruct _. reflexivity. TMcrush.
      + TMcrush. right.
        repeat econstructor; eauto.
        rewrite H0 in H4; destruct l0; inv H4; reflexivity.
      + right. subst. TMcrush.
      + right. TMcrush.
        repeat econstructor. rewrite H6 in H7.
        rewrite H7. rewrite H6 in H4. destruct l0; inv H4.
        cbn. reflexivity.
  Qed.
    
  Lemma Copy_tapes_until_term :
    Copy_tapes_until ↓ liftT_gen [| Fin.of_nat_lt i_is_a_tape; Fin.of_nat_lt j_is_a_tape |]%vector_scope
                  (fun x i =>
                     i >= 9 + (|right (get_at tape_0 x)| +
                         match current (get_at tape_0 x) with Some _ => 1 | _ => 0 end) * 9).
  Proof.
    Existing Instance Copy_tapes_until_body_sem.
    TMcorrect.
    - unfold Copy_tapes_until_body_R. cbn -[mult].
      eapply functionalOn_lift_gen.
      hnf.
      intros ? ? ? ([ | ] & ? ) ([ | ] & ?) ? ?; firstorder; TMcrush.
      cbn in *. f_equal.
      
      eapply get_at_eq_iff; intros [ |[ | ]]; firstorder; try omega.
      + erewrite get_at_ext; rewrite ?H3, ?H2; symmetry; erewrite get_at_ext; rewrite ?H6, ?H4; eauto.
      +  erewrite get_at_ext; rewrite ?H3, ?H2; symmetry; erewrite get_at_ext; rewrite ?H6, ?H4; eauto. now inv H0.
    - cbn in *. intros. unfold liftT_gen in H. cbn in *.
      destruct (x[@i_is_a_tape]) eqn:E. cbn in *.
      exists x, false, i. firstorder. TMcrush. now left. 
      all:(try now  exists x, false, i; firstorder; cbn in *; rewrite E; firstorder).
      destruct (until e) eqn:Ee.
      now  exists x, false, i; firstorder; cbn in *; rewrite E; firstorder.
      pose (t0 := tape_move_right x[@i_is_a_tape]).
      pose (t1 := tape_move_right (midtape (left x[@j_is_a_tape]) e (right x[@j_is_a_tape]))).
      exists (Vector.replace (Vector.replace x j_is_a_tape t1) i_is_a_tape t0).
      exists true. exists 8. intuition; eauto.
      + unfold lift_gen_eq_p, lift_gen_p, runion, rintersection.
        cbn -[tape_move_right t0]. split.
        rewrite E. exists e. firstorder.
        * unfold get_at. rewrite Vector_replace_nth2.
         rewrite Vector_replace_nth. unfold t1. TMcrush. 
         intros L; eapply neq.
         assert (Fin.to_nat i_is_a_tape = Fin.to_nat j_is_a_tape) by congruence.
         rewrite !Fin.to_nat_of_nat in H0. congruence.
        * unfold get_at. rewrite Vector_replace_nth. unfold t0. TMcrush.
        * TMcrush.
      + simpl_TM. unfold liftT_gen. cbn.
        rewrite mult_comm in *. cbn in *.
        rewrite Vector_replace_nth. subst t0. subst t1.
        cbn in *. 
        unfold get_at in *. rewrite E. cbn.
        destruct _; cbn in *. omega. omega. 
  Qed.
      
End copy_tape_until.
