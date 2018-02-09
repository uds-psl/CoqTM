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

  Eval simpl in ltac:(intros ?e; destruct_shelve e) : (option (bool + (bool + (nat + nat)))) -> _.

  Lemma MatchSum_Sem : MatchSum ⊨c(5) MatchSum_Rel.
  Proof.
    eapply RealiseIn_monotone.
    { unfold MatchSum. repeat TM_Correct. }
    { Unshelve. 8: constructor. all: try omega. 3: constructor. cbn. omega. }
    {
      intros tin (yout&tout) H. destruct H as (H1&(t&(H2&H3)&H4)); hnf in *. subst.
      destruct_tapes; cbn in *.
      destruct h; cbn in *; TMSimp; eauto. destruct (map _) in H0; cbn in H0; congruence.
      destruct e; swap 1 2; cbn in *; TMSimp.
      - destruct s; swap 1 2; TMSimp.
        + destruct s; TMSimp; destruct v; cbn in *; inv H0.
        + destruct b; TMSimp.
          * destruct v as [vx|vy]; TMSimp. exists vx. split; auto.
            destruct (encode _) eqn:E; cbn; do 2 eexists; split; cbn; try rewrite E; cbn; auto.
          * destruct v as [vx|vy]; TMSimp. exists vy. split; auto.
            destruct (encode _) eqn:E; cbn; do 2 eexists; split; cbn; try rewrite E; cbn; auto.
      - destruct b; TMSimp; destruct v; TMSimp.
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
      { unfold ConstrSum. repeat TM_Correct. }
      { cbn. omega. }
      {
        TMSimp. destruct is_left; cbn in *; subst; TMSimp.
        {
          rewrite tape_match_right_left.
          destruct h; cbn in *; TMSimp.
          - destruct (encode _) in H0; cbn in *; congruence.
          - destruct (encode x) as [ | eX eXs] eqn:E;
              cbn in *; inv H0; cbv [tape_encodes_r]; cbn; rewrite E; cbn;
                (destruct x0; cbn; eauto).
        }
        {
          destruct h; cbn in *; TMSimp.
          - destruct (encode _) in H0; cbn in *; congruence.
          - destruct (encode y) as [ | eX eXs] eqn:E;
              cbn in *; inv H0; cbv [tape_encodes_r]; cbn; rewrite E; cbn;
                (destruct x; cbn; eauto).
        }
      }
    Qed.
                
      
  End SumConstr.

End MatchSum.


(* Reductions *)

Require Import ChangeAlphabet.

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
    - cbn. do 2 constructor.
    - eapply retr'.
  Defined.

  Lemma MatchOption_Sem :
    MatchOption ⊨c(5) MatchOption_Rel.
  Proof.
    eapply RealiseIn_monotone.
    {
      unfold MatchOption.
      eapply Lift_RealiseIn; swap 1 2. (* todo tac *)
      - eapply (MatchSum_Sem codX Encode_Unit).
      - eapply tight_retract_strong. cbn. eapply (ChangeAlphabet.retr' retr').
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
  Variable (sigX sigY sigZ : inhabitedFinType).
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

  (*
   * Erklärung der default-Werte:
   * Generell gilt, dass ein default-Symbol angegeben werden muss, dass nicht Teil der Kodierung der Ausgabe ist.
   * Die [MatchSum] Maschine arbeitet auf [X+Y], welches über [bool + (sigX + sigY)].
   * Diese wird auf das Alphabet [Bool + (sigX + sigY) + sigZ] geliftet.  Es muss also ein TRetract von [bool + (sigX + sigY)] nach
   * [Bool + (sigX + sigY) + sigZ] angegeben werden, der automatisch bestimmt wird.  Für die Zeichen in dem größeren Alphabet muss
   * ein Zeichen aus dem kleineren Alphabet angegeben werden, auf das die nicht zurück-übersetztbaren Zeichen gemappt wird.
   * Jetzt darf die Kodierung des Ergebnisses der Maschine (dies ist ein X bzw. ein Y, welches über sigX + sigY kodiert ist), das
   * [default]-Zeichen nicht enthalten.  Daher bietet sich [inl (default : bool)] an, i.e. die Injektion von einem beliebigen [bool].
   * M1 und M2 arbeiten jeweils über dem Alphabet [sigX + sigZ], bzw. [sigY + sigZ] und geben jeweils einen Z-Wert zurück, der über die
   * nach rechts gemappte Kodierung [sigX + sigZ] bzw. [sigY + sigZ].  In der Ausgabe darf also kein Symbol von [sigX] bzw. [sigY]
   * stehen. Dementsprechend wird die Injektion von [sigX] bzw. [sigY] als [default]-Symbol gewählt.
   *)
  
  Definition MapSum : { M : mTM (sig_add_sum ^+) n & states M -> unit } :=
    If (ChangeAlphabet (inl (default : bool)) _ (Inject (MatchSum sigX sigY) [|inputTape|]))
      (ChangeAlphabet (inl (default : sigX)) _ M1)
      (ChangeAlphabet (inl (default : sigY)) _ M2).



  Lemma MapSum_Computes : MapSum ⊫ Computes_Rel inputTape outputTape _ _ map_sum.
  Proof.
    eapply WRealise_monotone.
    {
      unfold MapSum. repeat TM_Correct.
      - unfold ChangeAlphabet. repeat TM_Correct. eapply RealiseIn_WRealise. eapply MatchSum_Sem.
      - simple eapply (ChangeAlphabet_Computes_WRealise _ _ f).
        + eapply M1_Computes.
        + left. intros. cbn. intros (?&?&?) % in_map_iff. inv H.
      - simple eapply (ChangeAlphabet_Computes_WRealise _ _ g).
        + eapply M2_Computes.
        + left. intros. cbn. intros (?&?&?) % in_map_iff. inv H.
    }
    { clear M1_Computes M2_Computes M1 M2. hnf. intros tin (()&tout). intros H. destruct_tapes; cbn in *.
      intros s H4. destruct H; destruct H as (tmid&H1&H2); hnf in H1, H2; cbn in H1, H2.
      {
        destruct H1 as (H1&H0); hnf in H0, H1. specialize (H1 s). spec_assert H1 as (x&->&H1).
        { eapply ChangeAlphabet.encodeTranslate_tau1 in H4. autounfold with tape. simpl_tape. eauto. }
        clear H0. subst; cbn. specialize (H2 x). spec_assert H2.
        { clear H2 H4. autounfold with tape in H1. simpl_tape in H1.
          eapply encodeTranslate_tau2 with (def := inr default).
          - left. cbn. intros (?&?&?) % in_map_iff. inv H.
          - eapply (encodeTranslate_tau2 _) in H1.
            eapply encodeTranslate_tau1. refine (tape_encodes_ext' _ _ H1); auto. cbn. rewrite !List.map_map. apply map_ext; auto.
            Unshelve. left. cbn. intros (?&?&?) % in_map_iff. cbn in *. unfold retract_comp_f in H. inv H.
        } 
        refine (tape_encodes_ext _ H2). cbn. now rewrite List.map_map.
      }
      {
        destruct H1 as (H1&H0); hnf in H0, H1. specialize (H1 s). spec_assert H1 as (y&->&H1).
        { eapply ChangeAlphabet.encodeTranslate_tau1 in H4. autounfold with tape. simpl_tape. eauto. }
        clear H0. subst; cbn. specialize (H2 y). spec_assert H2.
        { clear H2 H4. autounfold with tape in H1. simpl_tape in H1.
          eapply encodeTranslate_tau2 with (def := inr (default : sigZ)).
          - left. cbn. intros (?&?&?) % in_map_iff. inv H.
          - eapply (encodeTranslate_tau2 _) in H1.
            eapply encodeTranslate_tau1. refine (tape_encodes_ext' _ _ H1); auto. cbn. rewrite !List.map_map. apply map_ext; auto.
            Unshelve. left. cbn. intros (?&?&?) % in_map_iff. cbn in *. unfold retract_comp_f in H. inv H.
        } 
        refine (tape_encodes_ext _ H2). cbn. now rewrite List.map_map.
      }
    }
  Qed.
  
End MapSum.