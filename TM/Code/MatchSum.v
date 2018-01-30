Require Import TM.Code.CodeTM.
Require Import TM.Basic.Mono TM.Basic.Nop TM.Basic.Multi.
Require Import TM.Combinators.Combinators.
Require Import TM.LiftMN TM.LiftSigmaTau.
Require Import TM.Compound.TMTac.
Require Import TM.Compound.CopySymbols TM.Compound.MoveToSymbol.

(* Basic pattern matching *)
Section MatchSum.
  Variable X Y : Type.
  Variable (sigX sigY : finType).
  Hypothesis (codX : codeable sigX X) (codY : codeable sigY Y).

  Definition MatchSum_Rel : Rel (tapes (bool + (sigX+sigY))^+ 1) (bool * tapes (bool + (sigX+sigY))^+ 1) :=
    Mk_R_p (if? (fun (tin tout : tape (bool + (sigX+sigY))^+) =>
                   forall v : X + Y,
                     tin ≂ v ->
                     exists x : X, v = inl x /\ tout ≂ x)
              ! (fun (tin tout : tape ((bool + (sigX+sigY))^+)) =>
                   forall v : X + Y,
                     tin ≂ v ->
                     exists y : Y, v = inr y /\ tout ≂ y)).

  Definition MatchSum : { M : mTM (bool + (sigX+sigY))^+ 1 & states M -> bool } :=
    MATCH (Read_char _)
          (fun o => match o with
                 | Some (inr (inl true))  => Write (inl START) tt;; Move _ R true  (* inl *)
                 | Some (inr (inl false)) => Write (inl START) tt;; Move _ R false (* inr *)
                 | _ => mono_Nop _ true (* invalid input *)
                 end).

  Lemma MatchSum_Sem : MatchSum ⊨c(5) MatchSum_Rel.
  Proof.
    eapply RealiseIn_monotone.
    {
      unfold MatchSum. eapply Match_RealiseIn. cbn. eapply read_char_sem.
      instantiate (2 := fun o : option (bool + (sigX+sigY))^+ =>
                          match o with Some (inr (inl true)) => _ | Some (inr (inl false)) => _ | _ => _ end).
      cbn. intros [ s | ]; cbn.
      - destruct s as [ start | s]; cbn.
        + eapply RealiseIn_monotone'. eapply mono_Nop_Sem. omega.
        + destruct s as [cons | xy]; swap 1 2; cbn.
          * eapply RealiseIn_monotone'. eapply mono_Nop_Sem. omega.
          * destruct cons; (eapply Seq_RealiseIn; [eapply Write_Sem | eapply Move_Sem]).
      - eapply RealiseIn_monotone'. eapply mono_Nop_Sem. omega.
    }
    { cbn. omega. }
    {
      intros tin (yout&tout) H. destruct H as (H1&(t&(H2&H3)&H4)); hnf in *. subst.
      destruct_tapes; cbn in *.
      destruct h; cbn in *; TMSimp; eauto. destruct (map _) in H0; cbn in H0; congruence.
      destruct e; swap 1 2; cbn in *; TMSimp.
      - destruct s; swap 1 2; cbn in *; TMSimp.
        + destruct v; cbn in *; destruct (map _) in H0; cbn in *; congruence.
        + destruct b; TMSimp cbn in *.
          * destruct v as [vx|vy]; TMSimp. exists vx. split; auto.
            destruct (encode _) eqn:E; cbn; do 2 eexists; split; cbn; try rewrite E; cbn; auto.
          * destruct v as [vx|vy]; TMSimp. exists vy. split; auto.
            destruct (encode _) eqn:E; cbn; do 2 eexists; split; cbn; try rewrite E; cbn; auto.
      - destruct v; cbn in *.
        + destruct (map _) in H0; cbn in H0; inv H0.
        + destruct (map _) in H0; cbn in H0; inv H0.
    }
  Qed.

  (* Constructors *)
  Section SumConstr.

    Definition ConstrSum_Rel (is_left:bool) : Rel (tapes (bool + (sigX+sigY))^+ 1) (unit * tapes (bool + (sigX+sigY))^+ 1) :=
      Mk_R_p (
          ignoreParam
            (fun tin tout =>
               if is_left
               then forall x : X, tape_encodes (Encode_Map codX (@retract_r_l sigX sigY)) tin x ->
                             tape_encodes (Encode_Sum codX codY) tout (inl x)
               else forall y : Y, tape_encodes (Encode_Map codY (@retract_r_r sigX sigY)) tin y ->
                             tape_encodes (Encode_Sum codX codY) tout (inr y))).

    Definition ConstrSum (is_left:bool) : { M : mTM (bool + (sigX+sigY))^+ 1 & states M -> unit } :=
      Move _ L tt;; Write (inr (inl is_left)) tt;; Move _ L tt;; Write (inl START) tt;; Move _ R tt.

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


(* Reduction *)

Require ChangeAlphabet.

Section MatchOption.

  (* Matching of option reduces to matching of sums with [Empty_set] *)

  Variable X : Type.
  Variable (sigX : finType).
  Hypothesis (codX : codeable sigX X).

  Compute encode None.
  Compute encode (Some 42).

  Definition MatchOption_Rel : Rel (tapes (bool + sigX)^+ 1) (bool * tapes (bool + sigX)^+ 1) :=
    Mk_R_p (if? (fun (tin tout : tape (bool + sigX)^+) =>
                   forall v : option X,
                     tape_encodes (Encode_Option codX ) tin v ->
                     exists x : X, v = Some x)
              ! (fun (tin tout : tape (bool + sigX)^+) =>
                   forall v : option X,
                     tape_encodes (Encode_Option codX ) tin v ->
                     v = None)).

  Let retr' : TRetract (bool + (sigX + Empty_set)) (bool + sigX) .
  Proof. econstructor. eapply tretract_sum; auto_inj. Defined.
    
  Definition MatchOption : { M : mTM (bool + sigX)^+ 1 & states M -> bool }.
  Proof.
    eapply ChangeAlphabet.ChangeAlphabet. 3: eapply (@MatchSum sigX (FinType (EqType Empty_set))).
    - eapply retr'.
    - cbn. do 2 constructor.
  Defined.


  
  Lemma MatchOption_Sem :
    MatchOption ⊨c(5) MatchOption_Rel.
  Proof.
    eapply RealiseIn_monotone.
    {
      unfold MatchOption. eapply LiftSigmaTau.Lift_RealiseIn.
      - eapply tight_retract_strong. cbn. eapply (ChangeAlphabet.retr' retr').
      - eapply (MatchSum_Sem codX Encode_Unit).
    }
    { omega. }
    {
      hnf. intros tin (yout&tout). intros H. destruct_tapes; cbn in *.
      hnf in *. destruct yout; cbn in *.
      {
        intros [ v | ] Hv; cbn in *.
        - specialize (H (inl v)).
          spec_assert H as (x&H).
          {
            destruct Hv as (r1&r2&Hv1&Hv2); cbn in *.
            eapply (ChangeAlphabet.encodeTranslate_tau1 (inl true) (retr := retr')).
            hnf. do 2 eexists. split. exact Hv1. exact Hv2.
          }
          inv H. eauto.
        - specialize (H (inr tt)).
          spec_assert H as (x&H1&H2).
          {
            destruct Hv as (r1&r2&Hv1&Hv2); cbn in *.
            eapply (ChangeAlphabet.encodeTranslate_tau1 (inl true) (retr := retr')).
            hnf. do 2 eexists. split. exact Hv1. exact Hv2.
          }
          inv H1.
      }
      {
        intros [ v | ] Hv; cbn in *.
        - specialize (H (inl v)).
          spec_assert H as (x&H1&H2).
          {
            destruct Hv as (r1&r2&Hv1&Hv2); cbn in *.
            eapply (ChangeAlphabet.encodeTranslate_tau1 (inl true) (retr := retr')).
            hnf. do 2 eexists. split. exact Hv1. exact Hv2.
          }
          inv H1.
        - specialize (H (inr tt)).
          spec_assert H as (x&H).
          {
            destruct Hv as (r1&r2&Hv1&Hv2); cbn in *.
            eapply (ChangeAlphabet.encodeTranslate_tau1 (inl true) (retr := retr')).
            hnf. do 2 eexists. split. exact Hv1. exact Hv2.
          }
          inv H. eauto.
      }
    }
  Qed.

End MatchOption.


(* TODO: Konstruktor für Listen *)


(* TODO: Match für Zahlen: von Listen-Match ableiten *)


Section MapSum.

  Variable n : nat.
  Variable (sigX sigY sigZ : finType).
  Variable (X Y Z : Type) (codX : codeable sigX X) (codY : codeable sigY Y) (codZ : codeable sigZ Z).

  Variable (inputTape outputTape : Fin.t n).
  
  Local Definition sig_add_sum : finType := FinType(EqType((bool+(sigX+sigY))+sigZ)).
  Local Definition sig_add_X : finType := FinType(EqType(sigX+sigZ)).
  Local Definition sig_add_Y : finType := FinType(EqType(sigY+sigZ)).

  Variable f : X -> Z.
  Variable g : Y -> Z.

  Variable M1 : { M : mTM (sig_add_X ^+) n & states M -> unit }.
  Variable M2 : { M : mTM (sig_add_Y ^+) n & states M -> unit }.

  Hypothesis M1_Computes : M1 ⊫ Computes_Rel inputTape outputTape _ _ f.
  Hypothesis M2_Computes : M2 ⊫ Computes_Rel inputTape outputTape _ _ g.

  Definition map_sum : X + Y -> Z :=
    fun s => match s with
          | inl x => f x
          | inr y => g y
          end.
  
  Variable (defX : sigX) (defY : sigY) (defZ : sigZ).

  Definition MapSum : { M : mTM (sig_add_sum ^+) n & states M -> unit } :=
    If (ChangeAlphabet.ChangeAlphabet _ (inr (inl defX)) (Inject (MatchSum sigX sigY) [|inputTape|]))
      (ChangeAlphabet.ChangeAlphabet _ (inl defX) M1)
      (ChangeAlphabet.ChangeAlphabet _ (inl defY) M2).

  Hypothesis DefX : forall x : X, ~ defX el encode x \/ (forall t' : sigX + sigZ, exists s' : sigX, retract_inl_g t' = Some s').
  Hypothesis DefY : forall y : Y, ~ defY el encode y \/ (forall t' : sigY + sigZ, exists s' : sigY, retract_inl_g t' = Some s').

  Lemma MapSum_Computes : MapSum ⊫ Computes_Rel inputTape outputTape _ _ map_sum.
  Proof.
    eapply WRealise_monotone.
    {
      unfold MapSum. eapply If_WRealsie.
      - eapply LiftSigmaTau.Lift_WRealise.
        + eapply tight_retract_strong. cbn. refine (ChangeAlphabet.retr' _).
        + eapply Inject_WRealise.
          * vector_dupfree.
          * eapply Realise_WRealise, RealiseIn_Realise. apply (MatchSum_Sem codX codY).
      - apply (ChangeAlphabet.ChangeAlphabet_Computes_WRealise _ (inl defX) f).
        + left. intros. cbn. intros (?&?&?) % in_map_iff. congruence.
        + eapply M1_Computes.
      - apply (ChangeAlphabet.ChangeAlphabet_Computes_WRealise _ (inl defY) g).
        + left. intros. cbn. intros (?&?&?) % in_map_iff. congruence.
        + eapply M2_Computes.
    }
    { clear M1_Computes M2_Computes M1 M2. hnf. intros tin (()&tout). intros H. destruct_tapes; cbn in *.
      intros s H4. destruct H; destruct H as (tmid&H1&H2); hnf in H1, H2; cbn in H1, H2.
      {
        destruct H1 as (H1&H0); hnf in H0, H1. specialize (H1 s). spec_assert H1 as (x&->&H1).
        {
          eapply ChangeAlphabet.encodeTranslate_tau1 in H4.
          unfold LiftSigmaTau.surjectTapes, LiftSigmaTau.surjectTape, LiftSigmaTau.mapTapes in *. cbn in *.
          erewrite VectorSpec.nth_map; try reflexivity; try exact H4.
        } subst; cbn. specialize (H2 x). spec_assert H2.
        { clear H4 H2.
          eapply (ChangeAlphabet.encodeTranslate_tau1) in H1. eapply (ChangeAlphabet.encodeTranslate_tau2 (def := inr defZ)).
          - left. cbn. intros (?&?&?)%in_map_iff. congruence.
          - eapply (ChangeAlphabet.encodeTranslate_tau2 (def := defX)).
            + cbn. auto.
            + refine (tape_encodes_ext' _ _ H1); auto.
              (* TODO: Automatisieren! Vectoren, autounfold von surjectTapes, etc. *)
              unfold ChangeAlphabet.surjectTape, LiftSigmaTau.surjectTapes, LiftSigmaTau.surjectTape, LiftSigmaTau.mapTapes in *.
              cbn. erewrite !VectorSpec.nth_map; eauto. rewrite !LiftSigmaTau.mapTape_mapTape. cbn.
              eapply LiftSigmaTau.mapTape_ext; intros. destruct a; cbn; auto. do 3 (destruct s; cbn; auto).
        } 
        refine (tape_encodes_ext _ H2). cbn. now rewrite List.map_map.
      }
      {
        destruct H1 as (H1&H0); hnf in H0, H1. specialize (H1 s). spec_assert H1 as (x&->&H1).
        {
          eapply ChangeAlphabet.encodeTranslate_tau1 in H4.
          unfold LiftSigmaTau.surjectTapes, LiftSigmaTau.surjectTape, LiftSigmaTau.mapTapes in *. cbn in *.
          erewrite VectorSpec.nth_map; try reflexivity; try exact H4.
        } subst; cbn. specialize (H2 x). spec_assert H2.
        { clear H4 H2.
          eapply (ChangeAlphabet.encodeTranslate_tau1) in H1. eapply (ChangeAlphabet.encodeTranslate_tau2 (def := inr defZ)).
          - left. cbn. intros (?&?&?)%in_map_iff. congruence.
          - eapply (ChangeAlphabet.encodeTranslate_tau2 (def := defY)).
            + cbn. auto.
            + refine (tape_encodes_ext' _ _ H1); auto.
              unfold ChangeAlphabet.surjectTape, LiftSigmaTau.surjectTapes, LiftSigmaTau.surjectTape, LiftSigmaTau.mapTapes in *.
              cbn. erewrite !VectorSpec.nth_map; eauto. rewrite !LiftSigmaTau.mapTape_mapTape. cbn.
              eapply LiftSigmaTau.mapTape_ext; intros. destruct a; cbn; auto. do 3 (destruct s; cbn; auto).
        } 
        refine (tape_encodes_ext _ H2). cbn. now rewrite List.map_map.
      }
    }
  Qed.
  
End MapSum.