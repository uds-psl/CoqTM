Require Import TM.Code.CodeTM.

Require Import TM.Basic.Mono TM.Basic.Nop TM.Basic.Multi.
Require Import TM.Combinators.Combinators.
Require Import TM.LiftMN.

Require Import TM.Compound.TMTac.
Require Import TM.Compound.CopySymbols TM.Compound.MoveToSymbol.



(* Basic pattern matching *)
Section MatchSum.
  Variable X Y : Type.
  Variable (sigX sigY : finType).
  Hypothesis (codX : codeable sigX X) (codY : codeable sigY Y).

  Definition MatchSum_Rel : Rel (tapes (sigX+sigY+bool)^+ 1) (bool * tapes (sigX+sigY+bool)^+ 1) :=
    Mk_R_p (if? (fun (tin tout : tape (sigX+sigY+bool)^+) =>
                   forall v : X + Y,
                     tape_encodes (Encode_Sum codX codY) tin v ->
                     exists x : X, v = inl x /\
                              tape_encodes (Encode_Map codX (@retract_l_l sigX sigY)) tout x)
              ! (fun (tin tout : tape (sigX+sigY+bool)^+) =>
                   forall v : X + Y,
                     tape_encodes (Encode_Sum codX codY) tin v ->
                     exists y : Y, v = inr y /\
                              tape_encodes (Encode_Map codY (@retract_l_r sigX sigY)) tout y)).

  Definition MatchSum : { M : mTM (sigX+sigY+bool)^+ 1 & states M -> bool } :=
    MATCH (Read_char _)
          (fun o => match o with
                 | Some (inl (inr true))  => Write (inr START) tt;; Move _ R true  (* inl *)
                 | Some (inl (inr false)) => Write (inr START) tt;; Move _ R false (* inr *)
                 | _ => mono_Nop _ true (* invalid input *)
                 end).

  Lemma MatchSum_Sem : MatchSum ⊨c(5) MatchSum_Rel.
  Proof.
    eapply RealiseIn_monotone.
    {
      unfold MatchSum. eapply Match_RealiseIn. cbn. eapply read_char_sem.
      instantiate (2 := fun o : option (sigX+sigY+bool)^+ =>
                          match o with Some (inl (inr true)) => _ | Some (inl (inr false)) => _ | _ => _ end).
      cbn. intros [ s | ]; cbn.
      - destruct s as [ s | start]; cbn.
        + destruct s as [xy | cons]; cbn.
          * eapply RealiseIn_monotone'. eapply mono_Nop_Sem. omega.
          * destruct cons; (eapply Seq_RealiseIn; [eapply Write_Sem | eapply Move_Sem]).
        + eapply RealiseIn_monotone'. eapply mono_Nop_Sem. omega.
      - eapply RealiseIn_monotone'. eapply mono_Nop_Sem. omega.
    }
    {
      cbn. omega.
    }
    {
      intros tin (yout&tout) H. destruct H as (H1&(t&(H2&H3)&H4)); hnf in *. subst.
      destruct_tapes; cbn in *.
      destruct h; cbn in *; TMSimp; eauto. destruct (map _) in H0; cbn in H0; congruence.
      destruct e; cbn in *; TMSimp.
      - destruct s; cbn in *; TMSimp.
        + destruct v; cbn in *; destruct (map _) in H0; cbn in *; congruence.
        + destruct b; cbn in *; TMSimp cbn in *; unfold encode_sum in *.
          * destruct v; TMSimp cbn in *. eexists; split; eauto.
            hnf. destruct (encode x1) eqn:E; cbn; do 2 eexists; split; hnf; cbn; eauto. all: rewrite E; cbn; eauto.
          * destruct v; TMSimp cbn in *. eexists; split; eauto.
            hnf. destruct (encode y) eqn:E; cbn; do 2 eexists; split; hnf; cbn; eauto. all: rewrite E; cbn; eauto.
      - destruct v; cbn in *.
        + destruct (map _) in H0; cbn in H0; inv H0.
        + destruct (map _) in H0; cbn in H0; inv H0.
    }
  Qed.

  (* Constructors *)
  Section SumConstr.

    Definition ConstrSum_Rel (is_left:bool) : Rel (tapes (sigX+sigY+bool)^+ 1) (unit * tapes (sigX+sigY+bool)^+ 1) :=
      Mk_R_p (
          ignoreParam
            (fun tin tout =>
               if is_left
               then forall x : X, tape_encodes (Encode_Map codX (@retract_l_l sigX sigY)) tin x ->
                             tape_encodes (Encode_Sum codX codY) tout (inl x)
               else forall y : Y, tape_encodes (Encode_Map codY (@retract_l_r sigX sigY)) tin y ->
                             tape_encodes (Encode_Sum codX codY) tout (inr y))).

    Definition ConstrSum (is_left:bool) : { M : mTM (sigX+sigY+bool)^+ 1 & states M -> unit } :=
      Move _ L tt;; Write (inl (inr is_left)) tt;; Move _ L tt;; Write (inr START) tt;; Move _ R tt.

    Lemma ConstrSum_Sem (is_left:bool) : (ConstrSum is_left) ⊨c(9) (ConstrSum_Rel is_left).
    Proof.
      eapply RealiseIn_monotone.
      {
        eapply Seq_RealiseIn. eapply Move_Sem. eapply Seq_RealiseIn.
        eapply Write_Sem. eapply Seq_RealiseIn. eapply Move_Sem.
        eapply Seq_RealiseIn. eapply Write_Sem. eapply Move_Sem.
      }
      {
        cbn. omega.
      }
      {
        TMSimp ( cbn [Vector.nth] in * ). destruct is_left; cbn in *; subst; TMSimp.
        {
          destruct h; cbn in *; TMSimp; cbn in *.
          - destruct (encode _) in H0; cbn in *; congruence.
          - destruct (encode x) as [ | eX eXs] eqn:E;
              cbn in *; inv H0; cbv [tape_encodes_r]; cbn; rewrite E; cbn;
                (destruct x0; cbn; eauto).
        }
        {
          destruct h; cbn in *; TMSimp; cbn in *.
          - destruct (encode _) in H0; cbn in *; congruence.
          - destruct (encode y) as [ | eX eXs] eqn:E;
              cbn in *; inv H0; cbv [tape_encodes_r]; cbn; rewrite E; cbn;
                (destruct x; cbn; eauto).
        }
      }
    Qed.
                
      
  End SumConstr.

End MatchSum.


(* TODO: Match operator for functions *)
(*

Section MatchSum_Fun.

  Variable n : nat.
  Variable k : nat.

  Variable (sigX sigY : finType).
  Variable Z : Type.
  Variable tpZ : Fin.t n.
  Hypothesis codZ : codeable (sigX+sigY+bool)^+ Z.
  Variable parF : param_genT (sigX+sigY+bool)^+ n (S k).
  Variable f : param_genF Z parF.

  Let f_param1 := Vector.hd parF.
  Let f_param1T := projT1 (fst f_param1).
  Let f_param1Enc := projT2 (fst f_param1).
  Let f_param1Tape := snd f_param1.

  Variable X : Type.
  Variable codX

  Variable para 


End MatchSum_Fun.


    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    


Section MatchTM.

  Variable sig : finType.
  Variable n : nat.
  Variable (F1 : finType).
  Variable (def : F1).
  Variable (pM : sig -> { M1 : mTM sig^+ n & states M1 -> F1}).

  Variable k : nat.
  Variable resType : Type.
  Variable resTape : Fin.t n.
  Hypothesis codRes : codeable sig resType.
  Variable params : param_genT sig n (S k).
  Variable f : param_genF resType params.

  Let param1 := Vector.hd params.
  Let param1T := projT1 (fst param1).
  Let param1Enc := projT2 (fst param1).
  Let param1Tape := snd param1.

  Definition matchTM : { M : mTM sig^+ n & states M -> F1}:=
    MATCH (Read_char_at (sig^+) param1Tape)
          (fun o : option (sig^+) =>
             match o with
             | Some (inl s) =>
               (* TODO: write True on param1T, move param1T to R, call pM s *)
               pM s
             | _ => Nop n _ def
             end).


  Section MatchOption.

    Variable cont_None : 
    
  End MatchOption.

End MatchTM.

*)