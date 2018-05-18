Require Import TM.Code.CodeTM.
Require Import TM.Basic.Mono TM.Basic.Nop TM.Basic.Multi.
Require Import TM.Combinators.Combinators.
Require Import TM.LiftMN TM.LiftSigmaTau.
Require Import TM.Compound.TMTac.
Require Import TM.Compound.CopySymbols TM.Compound.MoveToSymbol.


(* This is good *)
Local Arguments finType_CS (X) {_ _}.


(* Basic pattern matching *)
Section MatchSum.

  Variable X Y : Type.

  Variable (sigX sigY : finType).
  Hypothesis (codX : codable sigX X) (codY : codable sigY Y).

  Definition MatchSum_Rel : Rel (tapes ((bool + (sigX+sigY))^+) 1) (bool * tapes ((bool + (sigX+sigY))^+) 1) :=
    Mk_R_p (fun tin '(yout, tout) =>
              forall s : X + Y, tin ≃ s ->
                           match s with
                           | inl x => tout ≃ x /\ yout = true
                           | inr y => tout ≃ y /\ yout = false
                           end).


  Definition MatchSum : { M : mTM (bool + (sigX+sigY))^+ 1 & states M -> bool } :=
    Move _ R tt;; (* skip the [START] symbol *)
    MATCH (Read_char _) (* read the "constructor" symbol *)
          (fun o => match o with (* Write a new [START] symbol and terminate in the corresponding partion *)
                 | Some (inr (inl true))  => Write (inl START) true  (* inl *)
                 | Some (inr (inl false)) => Write (inl START) false (* inr *)
                 | _ => mono_Nop _ true (* invalid input *)
                 end).

  Lemma MatchSum_Sem : MatchSum ⊨c(5) MatchSum_Rel.
  Proof.
    eapply RealiseIn_monotone.
    { unfold MatchSum. repeat TM_Correct. }
    { Unshelve. 4,6: constructor. all: cbn. all: omega. }
    {
      intros tin (yout&tout) H.
      intros s HEncS. destruct HEncS as (ls&HEncS). TMSimp; clear_trivial_eqs. clear HEncS tin.
      destruct s as [x|y]; cbn in *; TMSimp.
      - (* s = inl x *) now repeat econstructor.
      - (* s = inr y *) now repeat econstructor.
    }
  Qed.

  (* Constructors *)
  Section SumConstr.


    Definition Constr_inl_Rel : Rel (tapes (bool + (sigX+sigY))^+ 1) (unit * tapes (bool + (sigX+sigY))^+ 1) :=
      Mk_R_p (ignoreParam (fun tin tout => forall x:X, tin ≃ x -> tout ≃ inl x)).

    Definition Constr_inr_Rel : Rel (tapes (bool + (sigX+sigY))^+ 1) (unit * tapes (bool + (sigX+sigY))^+ 1) :=
      Mk_R_p (ignoreParam (fun tin tout => forall y:Y, tin ≃ y -> tout ≃ inr y)).

    Definition Constr_inl : { M : mTM (bool + (sigX+sigY))^+ 1 & states M -> unit } :=
      WriteMove (Some (inr (inl true)), L) tt;; Write (inl START) tt.

    Definition Constr_inr : { M : mTM (bool + (sigX+sigY))^+ 1 & states M -> unit } :=
      WriteMove (Some (inr (inl false)), L) tt;; Write (inl START) tt.


    Lemma Constr_inl_Sem : Constr_inl ⊨c(3) Constr_inl_Rel.
    Proof.
      eapply RealiseIn_monotone.
      { unfold Constr_inl. repeat TM_Correct. }
      { cbn. reflexivity. }
      {
        intros tin (()&tout) H.
        cbn. intros x HEncX. destruct HEncX as (ls&HEncX). TMSimp; clear_trivial_eqs.
        repeat econstructor. f_equal. simpl_tape. cbn. reflexivity.
      }
    Qed.

    Lemma Constr_inr_Sem : Constr_inr ⊨c(3) Constr_inr_Rel.
    Proof.
      eapply RealiseIn_monotone.
      { unfold Constr_inr. repeat TM_Correct. }
      { cbn. reflexivity. }
      {
        intros tin (()&tout) H.
        Arguments tape_move : simpl never.
        cbn. intros y HEncY. destruct HEncY as (ls&HEncY). TMSimp; clear_trivial_eqs.
        cbv [tape_move_mono] in *. cbn in *.
        Arguments tape_move { _ _ _ } /.
        cbn [tape_move_mono tape_move] in *.
        
        
        repeat econstructor. f_equal. simpl_tape. cbn. simpl_tape. reflexivity.
      }
    Qed.

  End SumConstr.

End MatchSum.

(*

(** ** Reductions *)

(* TODO!!! *)

Require Import ChangeAlphabet LiftSigmaTau.

Section MatchOption.

  (* Matching of option reduces to matching of sums with [Empty_set] *)

  Variable X : Type.
  Variable (sigX : finType).
  Hypothesis (codX : codable sigX X).

  Compute encode None.
  Compute encode (Some 42).

  Let sig := FinType (EqType (bool + (sigX + Empty_set))).
  Let tau := FinType (EqType (bool + sigX)).

  Let retr : TRetract sig tau .
  Proof. econstructor. eapply tretract_sum; eauto. Defined.

  Let retr' : TRetract sig^+ tau^+.
  Proof. eapply ChangeAlphabet.retr'. eapply retr. Defined.

  Let def : sig := inl default.

  Local Instance codX' : codable sig X.
  Proof.
    eapply Encode_Map. eapply codX. unshelve eapply TRetr_inv. econstructor.
  Abort.

  Typeclasses eauto := debug.
  Check _ : codable tau^+ X.

  Definition MatchOption_Rel : Rel (tapes tau^+ 1) (bool * tapes tau^+ 1) :=
    Mk_R_p (fun tin '(yout, tout) =>
              forall o : option X,
                tin ≃ o ->
                match o with
                | Some x => tout ≃ x /\ yout = true
                | None => tout ≃ tt /\ yout = false
                end).

  Definition MatchOption : { M : mTM (bool + sigX)^+ 1 & states M -> bool }.
  Proof.
    eapply Lift.
    - cbn. eapply MatchSum with (sigX := sigX) (sigY := FinType (EqType Empty_set)).
    - apply TRetract_Retract. apply retr'.
    - refine [| inr def |].
  Defined.


  Lemma MatchOption_Sem :
    MatchOption ⊨c(5) MatchOption_Rel.
  Proof.
    eapply RealiseIn_monotone.
    { unfold MatchOption. eapply Lift_RealiseIn. eapply MatchSum_Sem with (X := X) (Y := Empty_set). }
    { cbn. reflexivity. }
    {
      intros tin (yout&tout) H. intros o HEncO.
      destruct HEncO as (ls&HEncO). destruct o as [x| ]; TMSimp.
      - specialize (H (inl x)). TMSimp. spec_assert H as (H&->).
        { repeat econstructor. cbn. unfold surjectTapes. simpl_vector. TMSimp. f_equal. f_equal.
          rewrite List.map_app, !List.map_map. cbn. reflexivity. }
        autounfold with tape in H. simpl_vector in H. cbn in *.
        split; auto.
        Typeclasses eauto := debug.
        Check contains_translate_tau2 (sig := sig) (tau := tau) (retr := retr) (enc_X := codX).
        cbn in *.
        unfold tape_contains in *.
        Set Printing Implicit.
        cbn in *.
        .

        Show Existentials.

        instantiate (1 := ltac:(print_goal_cbn)).


        





      
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
  Variable (X Y Z : Type) (codX : codable sigX X) (codY : codable sigY Y) (codZ : codable sigZ Z).

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
          - unshelve eapply (encodeTranslate_tau2 _) in H1.
            + left. cbn. intros (?&?&?) % in_map_iff. cbn in *. unfold retract_comp_f in H. inv H.
            + eapply encodeTranslate_tau1. refine (tape_encodes_ext' _ _ H1); auto. cbn. rewrite !List.map_map. apply map_ext; auto.
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
          - unshelve eapply (encodeTranslate_tau2 _) in H1.
            + left. cbn. intros (?&?&?) % in_map_iff. cbn in *. unfold retract_comp_f in H. inv H.
            + eapply encodeTranslate_tau1. refine (tape_encodes_ext' _ _ H1); auto. cbn. rewrite !List.map_map. apply map_ext; auto.
        }
        refine (tape_encodes_ext _ H2). cbn. now rewrite List.map_map.
      }
    }
  Qed.

End MapSum.

*)