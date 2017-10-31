Require Export TM Nop.
Require Import Shared.FiniteTypes.DepPairs EqdepFacts.

Section While.

  Variable n : nat.
  Variable sig : finType.

  Variable pM : { M : mTM sig n & states M -> bool }.
  
  Definition while_trans :
    (TM.states (projT1 pM)) * Vector.t (option sig) n ->
    (TM.states (projT1 pM)) * Vector.t (option sig * move) n :=
    fun st => let (s,a) := st in
           if projT2 pM s && halt s then (start (projT1 pM),null_action) else trans st.

  Definition While : mTM sig n :=
    Build_mTM while_trans (start (projT1 pM))
              (fun s => halt s && negb (projT2 pM s)).

  Definition WHILE := (While; fun _ => tt).

  Local Arguments loopM {_ _} _ _ _.
  Local Arguments halt {_ _} _ _.
  Local Arguments step {_ _} _ _.


  Definition unlift_1 : mconfig sig (states While) n -> option (mconfig sig (states (projT1 pM)) n).
  Proof.
    intros s. exact (if (halt (projT1 pM) (cstate s)) then Some s else None).
  Defined.
 
  Lemma While_split i res c:
    loopM While i c = Some res ->
    (exists i1 x1 i2,  loopM (projT1 pM) i1 c = Some x1 /\
                     loopM While i2 x1 = Some res /\ i = i1 + i2 ).
  Proof.
    intros.
    unfold loopM in H.
    eapply loop_split with (p := fun c=> halt (projT1 pM) (cstate c)) in H.
    destruct H as (i1 & x1 & i2 & H1 & H2 & ->).
    -exists i1,x1,i2. split;[ |split;[exact H2|reflexivity]].
     eapply loop_lift with (lift:=id) in H1.
     +exact H1.
     +reflexivity.
     +unfold id.  intros. destruct x. unfold step. cbn in *. rewrite H. now rewrite andb_false_r.
    -intros b. unfold halt at 2. cbn. now intros ->. 
  Qed.

  Lemma While_true_split i (x : mconfig _ (states While) _) oenc :
    halt (projT1 pM) (cstate x) = true  -> projT2 pM (cstate x) = true->
    loopM While i x = Some oenc ->
    exists i', i = 1+i' /\ loopM While i' (initc While (ctapes x)) = Some oenc.
  Proof.
    intros hx px Eq.
    destruct i as [ |i'];cbn in Eq;cbn in Eq; change (states (projT1 pM)) with (states While) in Eq; rewrite hx,px in Eq;cbn in Eq; inv Eq.
    exists i'. split;[omega| ].
    destruct x. cbn in *. rewrite <- H0. unfold loopM. f_equal.
    unfold step. cbn -[tape_move_multi null_action]. 
    rewrite hx,px. cbn -[tape_move_multi null_action]. now rewrite tape_move_null_action.
  Qed.

  Lemma While_true_merge i1 i2 (t x1 : mconfig _ (states While) _) oenc :
    loopM (projT1 pM) i1 t = Some x1 ->
    loopM While i2 (initc While (ctapes x1)) = Some oenc ->
    (projT2 pM) (cstate x1) = true ->
    loopM While (i1+(1+i2)) t = Some oenc.
  Proof.
    intros Eq1 Eq2 px1.
    eapply loop_merge with
    (p:= fun c => halt (projT1 pM) (cstate c)) (a2:=x1).
    {unfold While. cbn. intros. now destruct halt. }
    {change (states While) with (states (projT1 pM)) in *.
     eapply loop_lift with (g:= step While) in Eq1;[exact Eq1|reflexivity| ].
     intros. unfold step,While,while_trans. cbn. now rewrite H,andb_false_r.
    }
    cbn. assert (hx1:halt (projT1 pM) (cstate x1)=true) by (apply loop_fulfills_p in Eq1;now destruct halt).
    change (states While) with (states (projT1 pM)) in *.
    rewrite hx1;cbn.
    -rewrite <- Eq2. unfold loopM. cbn. f_equal. unfold step. cbn -[tape_move_multi null_action].
     rewrite hx1,px1;cbn -[tape_move_multi null_action]. now rewrite tape_move_null_action. 
  Qed.

   Lemma While_false_merge i1 (t : mconfig _ (states While) _) oenc :
    loopM (projT1 pM) i1 t = Some oenc ->
    projT2 pM (cstate oenc) = false ->
    loopM While i1 t = Some oenc.
  Proof.
    intros Eq px1.
    eapply (loop_unlift (unlift := fun (x:mconfig sig (states While) n) => Some x))
      in Eq. destruct Eq as (?&H'&H1). inv H1.
    Focus 3. intros ? ? H. inv H. reflexivity.
    replace i1 with (i1+0) by omega.
    eapply (loop_merge (p:= fun c => halt (projT1 pM) (cstate c))). unfold halt at 2. cbn. 
    now intros ? ->. exact H'.
    apply loop_fulfills_p_0. unfold halt. cbn. rewrite px1.
    apply loop_fulfills_p in H'. now destruct halt.
    intros ? ? H ?. inv H. eexists. split;[ |reflexivity].
    cbn in H0. f_equal. unfold step at 2;cbn. rewrite H0. now rewrite andb_false_r.  reflexivity. 
  Qed.
    
  Lemma While_Realise (R : Rel _ (bool * _)) :
    pM ⊫ R ->
    WHILE ⊫ ( (star (R |_ true)) ∘ (ignoreParam (R |_ false))).
  Proof.
    intros HR t1 i1 oenc2 eq. unfold initc in eq.
    revert t1 eq; apply complete_induction with (x:=i1); clear i1; intros i1 IH t1 eq.
    apply While_split in eq as (i2&x0&i3&Eq1&Eq2&->).
    assert (hx0 : halt (projT1 pM) (cstate x0) = true)
      by (eapply loop_fulfills_p in Eq1;  destruct halt;auto).
    destruct (projT2 pM (cstate x0)) eqn: px0.
    -apply While_true_split in Eq2 as (i' & -> & Eq2);[ |assumption..].
     apply IH in Eq2;[ |omega].
     eapply use_subrel.
     rewrite <- star_rcomp_idem. rewrite rcomp_assoc. reflexivity.
     exists (ctapes x0);split.
     +apply R_in_star.
      apply HR in Eq1. cbn in Eq1. now rewrite px0 in Eq1.
     +assumption.
    -exists t1. split;[now apply starR| ]. hnf.
     unfold loopM in Eq2; rewrite loop_fulfills_p_0 in Eq2;[ |cbn;now rewrite hx0, px0]. inv Eq2.
     apply HR in Eq1. cbn in Eq1. now rewrite px0 in Eq1.
  Qed.


  (*
  (* TODO Versuche erst das zu beweisen und daraus das induktive Ding unten zu zeigen *)
  Lemma While_terminatesIn' t :

    pM ↓(T) ->
    (forall (x : tapes sig n) '(y, i),
        T' x (y, i) -> exists (x':tapes _ _) (b:bool) i1 y1,
           T x (y1,i1) /\ if b then exists i2 y2, T' x' (y2, i2) /\ i1+1+i2<=i else i1 <= i)->
    WHILE ↓(T').
  Proof.
    intros Term_M Hyp. hnf.
    intros t i. revert t. apply complete_induction with (x:=i); clear i; intros i IH t T't.
    destruct (Hyp _ _ T't) as (t'& b& i1&Rx&Tx&H).
    destruct b.
    -destruct H as (i2&T't'&Leq).
     apply IH in T't' as (oenc & Eq);[ |omega].
     exists oenc.
     apply Term_M in Tx as (oenc1 & Eq1).
     apply (loop_ge (k1:=i1 + (1 + i2)));[omega| ].
     specialize (HR _ _ _ Eq1). specialize (Func _ _ T't _ _ HR Rx). inv Func.
     now apply (While_true_merge Eq1).
    -apply Term_M in Tx as [oenc Eq].
     exists oenc.
     eapply While_false_merge. eapply loop_ge;[ |exact Eq]. omega.
     specialize (HR _ _ _ Eq).
     specialize (Func _ _ T't _ _ HR Rx). now inv Func.
  Qed.
*)

  (*
  Section WhileTerm.

    Inductive WhileTerm : Rel (tapes sig n) (unit * nat) :=
    | term_false input i          : T input (false, i) -> WhileTerm input (tt, i)
    | term_true  input i j output : T input (true,  i) -> WhileTerm output (tt, j) -> WhileTerm input (tt, i+1+j).

  End WhileTerm.
  
  
  Lemma While_Terminates (T : Rel _ (_ * nat)):
    pM ↓(T) -> WHILE ↓(WhileTerm T).
  Proof.
    intros Term. hnf. intros t1. specialize (Term t1) as (c1&i1&eq&Term).
    revert t1 eq Term; apply complete_induction with (x:=i1); clear i1; intros i1 IH t1 eq Term.
    destruct c1 as [b tapes1].
    destruct (



  Restart.
  Proof.
    intros HR Term_M Func Hyp.
    intros t i. revert t. apply complete_induction with (x:=i); clear i; intros i IH t T't.
    destruct (Hyp _ _ T't) as (t'& b& i1&Rx&Tx&H).
    destruct b.
    -destruct H as (i2&T't'&Leq).
     apply IH in T't' as (oenc & Eq);[ |omega].
     exists oenc.
     apply Term_M in Tx as (oenc1 & Eq1).
     apply (loop_ge (k1:=i1 + (1 + i2)));[omega| ].
     specialize (HR _ _ _ Eq1). specialize (Func _ _ T't _ _ HR Rx). inv Func.
     now apply (While_true_merge Eq1).
    -apply Term_M in Tx as [oenc Eq].
     exists oenc.
     eapply While_false_merge. eapply loop_ge;[ |exact Eq]. omega.
     specialize (HR _ _ _ Eq).
     specialize (Func _ _ T't _ _ HR Rx). now inv Func.
  Qed.
*)

End While.
(* Arguments While {n} {sig} M _. *)
