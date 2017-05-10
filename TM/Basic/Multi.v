Require Import Basic.

Section par_move_step.

  Variable sig : finType.
  Variable tapes_no : nat.

  Variable tape_i : nat.
  Hypothesis i_is_a_tape : tape_i < S tapes_no.

  Variable tape_j : nat.
  Hypothesis j_is_a_tape : tape_j < S tapes_no.
  
  Variable D : TM.move.

  Definition states := Fin.t 3.

  Definition pm_start : states := Fin.F1.
  Definition pm_true  : states := Fin.FS (Fin.F1).
  Definition pm_false : states := Fin.FS (Fin.FS (Fin.F1)).
  
  Definition par_move_trans (p : states * Vector.t (option sig) (S tapes_no)) : states * Vector.t (option sig * move) (S tapes_no) :=
    let (s,a) := p in
    match s with
    | Fin.F1 => match get_at i_is_a_tape a with
               | None => (pm_false, null_action)
               | Some c => match get_at j_is_a_tape a with
                          | None => (pm_false, null_action)
                          | Some c' => (pm_true, do_on_tapes tape_i tape_j (None, D))
                          end
               end
    | _ => (s, null_action)
    end.

  Definition parmove_step : mTM sig tapes_no :=
    Build_mTM par_move_trans pm_start (fun x => negb (Fin.eqb x pm_start)).
  
  Definition Parmove_step_R :=
    if?
        (fun t t' => exists c c' : sig,
             current (get_at tape_0 t) = Some c /\
             current (get_at tape_1 t) = Some c' /\
             get_at tape_0 t' = tape_move (get_at tape_0 t) D /\
             get_at tape_1 t' = tape_move (get_at tape_1 t) D)
        ! (fun t t' =>
             (current (get_at tape_0 t) = None \/
               current (get_at tape_1 t) = None)) ∩ (@IdR _).
                

  Definition Parmove_step := (parmove_step ; fun x : states => Fin.eqb x pm_true).
  
  Lemma Parmove_step_sem :
    Parmove_step ⊨(1) ⇑⇑[i_is_a_tape; j_is_a_tape] Parmove_step_R.
  Proof.
    cbn.
    intros t.
    destruct (current (get_at i_is_a_tape t)) eqn:E1.
    - destruct (current (get_at j_is_a_tape t)) eqn:E2.
      + exists (mk_mconfig pm_true (tape_move_multi t (do_on_tapes tape_i tape_j (None, D)))).
        simpl_TM. rewrite E1, E2. simpl_TM.
      + exists (mk_mconfig pm_false t).
        simpl_TM. rewrite E1, E2. simpl_TM.
    - exists (mk_mconfig pm_false t).
      simpl_TM. rewrite E1. simpl_TM.
  Qed.                             

End par_move_step.

Section copy.

  Variable sig : finType.
  Variable tapes_no : nat.

  Variable tape_i : nat.
  Hypothesis i_is_a_tape : tape_i < S tapes_no.

  Variable tape_j : nat.
  Hypothesis j_is_a_tape : tape_j < S tapes_no.
  
  Definition c_start : states := Fin.F1.
  Definition c_true  : states := Fin.FS (Fin.F1).
  Definition c_false : states := Fin.FS (Fin.FS (Fin.F1)).
  
  Definition copy_trans (p : states * Vector.t (option sig) (S tapes_no)) : states * Vector.t (option sig * move) (S tapes_no) :=
    let (s,a) := p in
    match s with
    | Fin.F1 => match get_at i_is_a_tape a with
               | None => (c_false, null_action)
               | Some c => match get_at j_is_a_tape a with
                          | None => (c_false, null_action)
                          | Some c' => (c_true, do_on_tape j_is_a_tape (Some c, TM.N))
                          end
               end
    | _ => (s, null_action)
    end.

  Definition copy : mTM sig tapes_no :=
    Build_mTM copy_trans c_start (fun x => negb (Fin.eqb x c_start)).

  Lemma copy_sem :
    copy ⊨(fun x : states => Fin.eqb x c_true,1)
         (fun t p =>
            let (b, t') := p in
            if b
            then
              (exists c c' : sig,
                  current (get_at i_is_a_tape t) = Some c /\
                  current (get_at j_is_a_tape t) = Some c' /\
                  (forall i (itape : i < S tapes_no), i <> tape_j -> get_at itape t = get_at itape t') /\
                  get_at j_is_a_tape t' = tape_write (get_at j_is_a_tape t) (Some c))
            else
              ( (current (get_at i_is_a_tape t) = None \/
                 current (get_at j_is_a_tape t) = None) /\
                t = t')).
  Proof.
    cbn.
    intros t.
    destruct (current (get_at i_is_a_tape t)) eqn:E1.
    - destruct (current (get_at j_is_a_tape t)) eqn:E2.
      + exists (mk_mconfig c_true (tape_move_multi t (do_on_tape j_is_a_tape (Some e, TM.N)))).
        simpl_TM.
        rewrite E1, E2. simpl_TM.
      + exists (mk_mconfig c_false t).
        simpl_TM. rewrite E1, E2. simpl_TM.
    - exists (mk_mconfig c_false t).
      simpl_TM. rewrite E1. simpl_TM.
  Qed.

End copy.


Section compare.

  Variable sig : finType.
  Variable tapes_no : nat.

  Variable tape_i : nat.
  Hypothesis i_is_a_tape : tape_i < S tapes_no.

  Variable tape_j : nat.
  Hypothesis j_is_a_tape : tape_j < S tapes_no.

  Definition compare_start : states := Fin.F1.
  Definition compare_true  : states := Fin.FS (Fin.F1).
  Definition compare_false : states := Fin.FS (Fin.FS (Fin.F1)).
  
  Definition compare_trans (p : states * Vector.t (option sig) (S tapes_no)) : states * Vector.t (option sig * move) (S tapes_no) :=
    let (s,a) := p in
    match s with
    | Fin.F1 => match get_at i_is_a_tape a with
               | None => (compare_false, null_action)
               | Some c => match get_at j_is_a_tape a with
                          | None => (compare_false, null_action)
                          | Some c' => if Decb (c = c')
                                      then (compare_true, null_action)
                                      else (compare_false, null_action)
                          end
               end
    | _ => (s, null_action)
    end.

  Definition compare_step : mTM sig tapes_no :=
    Build_mTM compare_trans compare_start (fun x => negb (Fin.eqb x compare_start)).

  Lemma compare_step_sem :
    compare_step ⊨(fun x : states => Fin.eqb x compare_true,1)
                 (fun t p =>
                    let (b, t') := p in
                    t = t' /\
                    if b
                    then
                      (exists c c' : sig,
                          current (get_at i_is_a_tape t) = Some c /\
                          current (get_at j_is_a_tape t) = Some c' /\
                          c = c')
                    else
                      ( (current (get_at i_is_a_tape t) = None \/
                         current (get_at j_is_a_tape t) = None \/
                         current (get_at i_is_a_tape t) <> current (get_at j_is_a_tape t)))).
  Proof.
    cbn.
    intros t.
    destruct (current (get_at i_is_a_tape t)) eqn:E1.
    - destruct (current (get_at j_is_a_tape t)) eqn:E2.
      + destruct (Decb (e = e0)) eqn:E3.
        *  exists (mk_mconfig compare_true t).
           simpl_TM.
           rewrite E1, E2, E3. simpl_TM. 
        * exists (mk_mconfig compare_false t). simpl_TM.
          rewrite E1, E2, E3. simpl_TM. decide (e = e0); cbn in *; firstorder congruence.
      + exists (mk_mconfig compare_false t).
        simpl_TM. rewrite E1, E2. simpl_TM.        
    - exists (mk_mconfig compare_false t).
      simpl_TM. rewrite E1. simpl_TM.
  Qed.

End compare.
