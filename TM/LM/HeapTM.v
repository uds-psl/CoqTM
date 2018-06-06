Require Import TM.Code.CodeTM TM.Code.Copy.
Require Import TM.Code.MatchNat TM.Code.MatchSum TM.Code.MatchFin TM.Code.MatchPair TM.Code.WriteValue.
Require Import TM.Code.ChangeAlphabet TM.LiftMN TM.LiftSigmaTau.
Require Import TM.Basic.Mono.
Require Import TM.Code.ListTM. (* [Nth] *)

Require Import TM.LM.Definitions TM.LM.TokTM.



(** * Heap Machine *)


(** ** Alphabets *)

(* See [TokTM] *)
Arguments sigTok : simpl never.

Definition sigHAd := FinType (EqType sigNat).
Arguments sigHAd : simpl never.

Definition sigPro := FinType (EqType (sigList sigTok)).
Arguments sigPro : simpl never.
Instance Encode_Prog : codable sigPro Pro := _.

Definition sigHClos := FinType (EqType (sigPair sigPro sigHAd)).
Arguments sigHClos : simpl never.
Instance Encode_HClos : codable sigHClos HClos := _.

Definition sigHEnt' := FinType (EqType (sigPair sigHClos sigHAd)).
Arguments sigHEnt' : simpl never.
Instance Encode_HEnt' : codable sigHEnt' (HClos*HAd) := _.

Definition sigHEnt := FinType (EqType (sigOption sigHEnt')).
Arguments sigHEnt : simpl never.
Instance Encode_Entr : codable sigHEnt HEnt := _.

Definition sigHeap := FinType (EqType (sigList sigHEnt)).
Arguments sigHeap : simpl never.
Instance Encode_Heap : codable sigHeap Heap := _.



(** ** Lookup *)

Fixpoint lookup (H:Heap) a n {struct n} : option (HClos) :=
  match n with
  | O =>
    match nth_error H a with
    | Some (Some (g, b)) => Some g
    | _ => None
    end
  | S n' =>
    match nth_error H a with
    | Some (Some (g, b)) => lookup H b n'
    | _ => None
    end
  end.

(*
There is no need to save [n], however [a] and [H] must be saved.
[H] and [a] are the parameters of [Nth], so they are already saved by [Nth].
However, in the [S n'] case, we overwrite [a] with [b], so we have to save [a] again.
(Actually, the first copy of [a] by [Nth] is superfluent, because we don't need a again during the loop.)
Because [Nth] has two internal tapes, and we need one addition tape to save [a], [Lookup] has 7 tapes in total:

t0: H
t1: a
t2: n
t3: out
t4-t5: internal tapes for [Nth]
t6: internal tape for storing the result of [Nth] in the case [n=0].
t7: saves [a]

The alphabet for [Lookup] can hold a Heap, an address, and an option of an entry, as well as an option of a closure.
*)


Definition sigLookup : finType := FinType (EqType ((sigHeap + sigNat + sigOption sigHEnt) + sigOption sigHClos)).
Arguments sigLookup : simpl never.

Check Retract_sigList_X.

Check _ : Retract sigNat sigLookup.


Check _ : codable sigLookup Heap.


Check _ : Retract sigNat sigLookup.



(** There are two ways to encode [nat] on [sigLookup]: First as a variable on [sigHeap], or directly using the provided [sigNat]. We neeed the alphabets [sigHeap], [sigNat], and [sigOption sigHEnt], which are in paranthesises in [sigLookup], for [Nth]. For simplicity, we assume that [a] and [n] are encoded directly in the latter way using [sigNat]. *)

Definition retr_nat_heap : Retract sigNat sigHeap := Retract_sigList_X _.
Definition retr1_nat : Retract sigNat sigLookup := Retract_inl (sigOption sigHClos) (Retract_inl (sigOption sigHEnt) (Retract_inl sigNat retr_nat_heap)).
Definition retr2_nat : Retract sigNat sigLookup := Retract_inl (sigOption sigHClos) (Retract_inl (sigOption sigHEnt) (Retract_inr sigHeap (Retract_id sigNat))).

Check _ : codable sigLookup (option HClos).
Check _ : codable sigLookup (option HEnt).
Check _ : codable sigLookup HEnt.

(*
Lookup_Step:

if n = S n' {
  buff = Nth H a
  if buff = Some (g, b) {
    (out, buff) = buff
    out = Some out
    return
  } else {
    Reset buff (* [MatchOption] currently resets the tape if the input was [None]. This could be considered a bug of [MatchOption], but it actually makes things more convenient. *)
    return
  }
} else if n = O {
  buff = Nth H a
  if buff = Some (g, b) {
    buff = snd buff
    Reset a; a <- buff
    Reset buff
    continue
  } else {
    Reset buff
    return
  }
}

t0: H
t1: a (copy)
t2: n
t3: out
t4-t5: internal tapes for [Nth]
t6: internal tape for storing the result of [Nth]
*)


Definition Lookup_Step : { M : mTM sigLookup^+ 7 & states M -> bool*unit } :=
  If (Inject (ChangeAlphabet MatchNat retr2_nat) [|Fin2|])
     (* [n = S n'] *)
     (Inject (ChangeAlphabet (Nth sigHEnt) _) [|Fin0; Fin1; Fin6; Fin4; Fin5|];;
      If (Inject (ChangeAlphabet (MatchOption sigHEnt) _) [|Fin6|])
         (If (Inject (ChangeAlphabet (MatchOption sigHEnt') _) [|Fin6|])
             (Return
                (Inject (ChangeAlphabet (Snd sigHClos sigHAd) _) [|Fin6|];;
                 Inject (ChangeAlphabet (Reset sigHAd) _) [|Fin1|];;
                 Inject (ChangeAlphabet (CopyValue sigHAd) (retr2_nat)) [|Fin6; Fin1|];;
                 Inject (ChangeAlphabet (Reset sigHAd) _) [|Fin6|])
                (true, tt))
             (Return (Inject (ChangeAlphabet (Constr_None sigHClos) _) [|Fin3|]) (false, tt)))
         (Return (Inject (ChangeAlphabet (Constr_None sigHClos) _) [|Fin3|]) (false, tt))
     )
     (* [n = O] *)
     (Return
        (Inject (ChangeAlphabet (Nth sigHEnt) _) [|Fin0; Fin1; Fin6; Fin4; Fin5|];;
         If (Inject (ChangeAlphabet (MatchOption sigHEnt) _) [|Fin6|])
            (If (Inject (ChangeAlphabet (MatchOption sigHEnt') _) [|Fin6|])
                (Inject (ChangeAlphabet (MatchPair sigHClos sigHAd) _) [|Fin6; Fin3|];;
                 Inject (ChangeAlphabet (Constr_Some sigHClos) _) [|Fin3|])
                (Inject (ChangeAlphabet (Constr_None sigHClos) _) [|Fin3|]))
            (Inject (ChangeAlphabet (Constr_None sigHClos) _) [|Fin3|]))
        (false, tt))
.



Definition Lookup_Step_Rel : Rel (tapes sigLookup^+ 7) (bool*unit * tapes sigLookup^+ 7) :=
  fun tin '(yout, tout) =>
    forall (H: Heap) (a n: nat),
      tin[@Fin0] ≃ H ->
      tin[@Fin1] ≃(Encode_map Encode_nat retr2_nat) a ->
      tin[@Fin2] ≃(Encode_map Encode_nat retr2_nat) n ->
      isRight tin[@Fin3] -> isRight tin[@Fin4] -> isRight tin[@Fin5] -> isRight tin[@Fin6] ->
      tout[@Fin0] ≃(Encode_map _ (Retract_inl _ _)) H /\
      match n with
      | O =>
        tout[@Fin1] ≃(Encode_map _ (Retract_inl _ _)) a /\
        tout[@Fin2] ≃(Encode_map _ (Retract_inl _ _)) 0 /\
        tout[@Fin3] ≃(Encode_map _ (Retract_inr _ _)) (* !!! *)
            match nth_error H a with
            | Some (Some (g, b)) => Some g
            | _ => None
            end /\
        yout = (false, tt)
      | S n' =>
        match nth_error H a with
        | Some (Some (g, b)) =>
          tout[@Fin1] ≃(Encode_map _ (Retract_inl _ _)) b /\
          isRight tout[@Fin3] /\
          yout = (true, tt)
        | _ =>
          tout[@Fin1] ≃(Encode_map _ (Retract_inl _ _)) a /\
          tout[@Fin3] ≃(Encode_map _ (Retract_inr _ _)) @None HClos /\ (* !!! *)
          yout = (false, tt)
        end /\
        tout[@Fin2] ≃(Encode_map _ (Retract_inl _ _)) n'
      end /\
      isRight tout[@Fin4] /\ isRight tout[@Fin5] /\ isRight tout[@Fin6]
.


Ltac clear_tape_eqs :=
  repeat match goal with
         | [ H: ?t'[@ ?x] = ?t[@ ?x] |- _ ] => clear H
         end.

Lemma Lookup_Step_Realise : Lookup_Step ⊨ Lookup_Step_Rel.
Proof.
  eapply Realise_monotone.
  { unfold Lookup_Step. repeat TM_Correct. all: unfold ChangeAlphabet; apply Lift_Realise.
    (* branche [n = S n' ] *)
    - eapply RealiseIn_Realise. apply MatchNat_Sem.
    - apply Nth_Computes with (X := HEnt).
    - eapply RealiseIn_Realise. apply MatchOption_Sem with (X := HEnt).
    - eapply RealiseIn_Realise. apply MatchOption_Sem with (X := (HClos * HAd) % type).
    - apply Snd_Realise with (X := HClos) (Y := HAd).
    - apply Reset_Realise with (X := nat).
    - apply CopyValue_Realise with (X := nat).
    - apply Reset_Realise with (X := nat).
    - eapply RealiseIn_Realise. apply Constr_None_Sem with (X := HClos).
    - eapply RealiseIn_Realise. apply Constr_None_Sem with (X := HClos).
    (* branche [n = O] *)
    - apply Nth_Computes with (X := HEnt).
    - eapply RealiseIn_Realise. apply MatchOption_Sem with (X := HEnt).
    - eapply RealiseIn_Realise. apply MatchOption_Sem with (X := (HClos * HAd) % type).
    - apply MatchPair_Realise with (X := HClos) (Y := HAd).
    - eapply RealiseIn_Realise. apply Constr_Some_Sem with (X := HClos).
    - eapply RealiseIn_Realise. apply Constr_None_Sem with (X := HClos).
    - eapply RealiseIn_Realise. apply Constr_None_Sem with (X := HClos).
  }
  {
    intros tin ((yout&()), tout) H.
    intros heap a n HEncH HEncA HEncN HRight3 HRight4 HRight5 HRight6.
    TMSimp; clear_trivial_eqs (*; clear_tape_eqs *).
    destruct H; TMSimp; clear_trivial_eqs. (* This takes ***LONG*** *)
    { (* Then branche of [MatchNat]: [n = S n'] *)
      unfold tape_contains in *.
      specialize (H n). spec_assert H by now apply contains_translate_tau1.
      
      destruct n; cbn in *; destruct H as (H&H'); inv H'.
      rename H0 into HCompNth.
      specialize (HCompNth heap a). spec_assert HCompNth.
      { apply contains_translate_tau1. apply (tape_contains_ext HEncH). cbn. now rewrite List.map_map. }
      spec_assert HCompNth.
      { apply contains_translate_tau1. apply (tape_contains_ext HEncA). cbn. now rewrite List.map_map. }
      spec_assert HCompNth by now apply surjectTape_isRight.
      spec_assert HCompNth by intros i; destruct_fin i; cbn; now apply surjectTape_isRight.
      destruct HCompNth as (HCompNth % contains_translate_tau2 & HCompNth2 % contains_translate_tau2 & HCompNth3 % contains_translate_tau2 & HCompNth4); cbn in *.
      specialize (HCompNth4 Fin1) as HCompNth5; specialize (HCompNth4 Fin0).
      
      destruct H1; TMSimp; clear_trivial_eqs (*; clear_tape_eqs *).
      { (* Then branche of first [MatchOption] *)
        rename H0 into HMatchOpt1.
        specialize (HMatchOpt1 (nth_error heap a)). spec_assert HMatchOpt1.
        { apply contains_translate_tau1. apply (tape_contains_ext HCompNth3). cbn. rewrite !List.map_map. apply map_ext. auto. }
        destruct (nth_error heap a) as [ hEnt | ] eqn:ENth; cbn in *; destruct HMatchOpt1 as (HMatchOpt1&HMatchOpt1'); inv HMatchOpt1'; apply contains_translate_tau2 in HMatchOpt1.

        destruct H1; TMSimp; clear_trivial_eqs (*; clear_tape_eqs *).
        { (* Then branche of second [MatchOption] *)
          rename H0 into HMatchOpt2; rename H2 into HMatchPair; rename H3 into HReset1; rename H4 into HCopy; rename H5 into HReset2.
          specialize (HMatchOpt2 hEnt); spec_assert HMatchOpt2.
          { apply contains_translate_tau1. apply (tape_contains_ext HMatchOpt1). cbn. now rewrite !List.map_map. }
          destruct hEnt as [ (g, b) | ]; cbn in *; destruct HMatchOpt2 as (HMatchOpt2,HMatchOpt2'); inv HMatchOpt2'; apply contains_translate_tau2 in HMatchOpt2.

          specialize (HMatchPair (g, b)); spec_assert HMatchPair as HMatchPair % contains_translate_tau2; cbn in *.
          { apply contains_translate_tau1. apply (tape_contains_ext (HMatchOpt2)). cbn. now rewrite List.map_map. }
          specialize (HReset1 a). spec_assert HReset1.
          { apply contains_translate_tau1.
            Search a.
            Search tmid1[@Fin1].
            Search tin[@Fin1].
            Search tmid[@Fin1].
            try apply (tape_contains_ext HEncA).
            admit.
          }
          specialize (HCopy b). spec_assert HCopy.
          { apply contains_translate_tau1. apply (tape_contains_ext HMatchPair). cbn. rewrite List.map_map. apply map_ext.
            cbn. 
            compute.
            cbv. 
          

          

    }
    { (* The Else branche of [MatchNat]: [n = 0] *)
      specialize (H n). spec_assert H.
      { apply contains_translate_tau1. apply (tape_contains_ext HEncN).
        cbn. rewrite !List.map_map, !map_app. f_equal; cbn; auto.
        apply map_ext. cbv.
        cbv [Retr_g] in H; cbn in H.
        unfold tape_contains in H.
      
      

      specialize (H n (contains_translate_tau1 HEncN)).
      
      
  }
Qed.




Definition Lookup_Loop := WHILE Lookup_Step.


(* Returns the [n] when [lookup] terminates *)
Fixpoint lookup_a (H:Heap) a n {struct n} : nat :=
  match n with
  | O => a
  | S n' =>
    match nth_error H a with
    | Some (Some (g, b)) => lookup_a H b n'
    | _ => a
    end
  end.


(* Returns the [n] when [lookup] terminates *)
Fixpoint lookup_n (H:Heap) a n {struct n} : nat :=
  match n with
  | O => 0
  | S n' =>
    match nth_error H a with
    | Some (Some (g, b)) => lookup_n H b n'
    | _ => n'
    end
  end.


Definition Lookup_Loop_Rel : Rel (tapes sigLookup^+ 7) (unit * tapes sigLookup^+ 7) :=
  ignoreParam (
      fun tin tout =>
        forall (H: Heap) (a n: nat),
          tin[@Fin0] ≃ H ->
          tin[@Fin1] ≃ a ->
          tin[@Fin2] ≃ n ->
          isRight tin[@Fin3] -> isRight tin[@Fin4] -> isRight tin[@Fin5] -> isRight tin[@Fin6] ->
          tout[@Fin0] ≃ H /\ (* [H] is saved *)
          tout[@Fin1] ≃ lookup_a H a n /\ (* the [a] when [lookup] terminated *)
          tout[@Fin2] ≃ lookup_n H a n /\ (* the [n] when [lookup] terminated *)
          tout[@Fin3] ≃ lookup H a n /\
          isRight tout[@Fin4] /\ (* internal tape of [Nth] *)
          isRight tout[@Fin5] /\ (* internal tape of [Nth] *)
          isRight tout[@Fin6] (* internal tape to save the result of [Nth] *)
    ).



Lemma Lookup_Loop_Realise : Lookup_Loop ⊨ Lookup_Loop_Rel.
Proof.
  eapply Realise_monotone.
  { unfold Lookup_Loop. repeat TM_Correct.
    - eapply Lookup_Step_Realise.
  }
  {
    apply WhileInduction; intros; intros H a n HEncH HEncA HEncN HRight3 HRight4 HRight5 HRight6.
    - hnf in HLastStep. specialize HLastStep with (1 := HEncH) (2 := HEncA) (3 := HEncN) (4 := HRight3) (5 := HRight4) (6 := HRight5) (7 := HRight6) as (HS1&HS2&HInt4&HInt5&HInt6).
      destruct n; [ destruct HS2 as (HEncA'&HEncN'&Hout&Hyout) | destruct HS2 as (HS2&HEncN')].
      + inv Hyout. cbn in *. destruct (nth_error H a) eqn:E; cbn in *; repeat split; auto.
      + cbn in *. destruct (nth_error H a) as [ e | ] eqn:E.
        * destruct e as [ (g,b) | ].
          -- destruct HS2 as (?&?&HS2); inv HS2.
          -- destruct HS2 as (?&?&?). repeat split; auto.
        * destruct HS2 as (?&?&?). repeat split; auto.
    - hnf in HStar. specialize HStar with  (1 := HEncH) (2 := HEncA) (3 := HEncN) (4 := HRight3) (5 := HRight4) (6 := HRight5) (7 := HRight6) as (HEncH'&HS2&HInt4&HInt5&HInt6).
      cbn in HLastStep.
      destruct n.
      + destruct HS2 as (HS2&HS3&HS4&HS5). inv HS5.
      + destruct HS2 as (HS2&HEncN').
        destruct (nth_error H a) as [  e | ] eqn:E.
        * destruct e as [ (g,b) | ].
          -- destruct HS2 as (HEncB&HRight3'&Hout). clear Hout.
             specialize HLastStep with (1 := HEncH') (2 := HEncB) (3 := HEncN') (4 := HRight3') (5 := HInt4) (6 := HInt5) (7 := HInt6) as (HLS1&HLS2&HLS3&HLS4&HLS5&HLS6&HLS7).
             cbn. repeat split; try rewrite E; auto.
          -- destruct HS2 as (?&?&HS2). inv HS2.
        * destruct HS2 as (?&?&HS2). inv HS2.
  }
Qed.



  
Definition Lookup_Rel : Rel (tapes sigLookup^+ 8) (unit * tapes sigLookup^+ 8) :=
  ignoreParam (
      fun tin tout =>
        forall (H: Heap) (a n: nat),
          tin[@Fin0] ≃ H ->
          tin[@Fin1] ≃ a ->
          tin[@Fin2] ≃ n ->
          isRight tin[@Fin3] -> isRight tin[@Fin4] -> isRight tin[@Fin5] -> isRight tin[@Fin6] -> isRight tin[@Fin7] ->
          tout[@Fin0] ≃ H /\ (* [H] is saved *)
          tout[@Fin1] ≃ a /\ (* [a] is saved *)
          isRight tout[@Fin2] /\ (* [n] is discarded *)
          tout[@Fin3] ≃ lookup H a n /\ (* output *)
          isRight tout[@Fin4] /\ (* internal tape of [Nth] *)
          isRight tout[@Fin5] /\ (* internal tape of [Nth] *)
          isRight tout[@Fin6] /\ (* internal tape to save the result of [Nth] *)
          isRight tout[@Fin7] (* internal tape to save [a] *)
    ).