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

Definition sigHA := FinType (EqType bool).
Arguments sigHA : simpl never.

Definition sigProg := FinType (EqType (sigHA + sigTok)).
Arguments sigProg : simpl never.
Local Instance Encode_Prop : codable sigProg Pro := _.

Definition sigHClos := FinType (EqType (sigProg + sigHA)).
Arguments sigHClos : simpl never.
Local Instance Encode_Clos : codable sigHClos HClos := _.

Definition sigHEnt' := FinType (EqType (sigHClos + sigHA)).
Arguments sigHEnt' : simpl never.

Definition sigHEnt := FinType (EqType (bool + sigHEnt')).
Arguments sigHEnt : simpl never.
Local Instance Encode_Entr : codable sigHEnt HEnt := _.

Definition sigHeap := FinType (EqType (bool + sigHEnt)).
Arguments sigHeap : simpl never.
Local Instance Encode_Heap : codable sigHeap Heap := _.



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

The alphabet for [Lookup] can hold a Heap, an address, and an option of a closure.
*)


(*
Inductive sigLookup : Type :=
| sigLookup_Heap (s : sigHeap)
| sigLookup_HA (s : sigHA)
| sigLookup_HClos (s : sigHClos)
.

Instance sigLookup_dec : eq_dec sigLookup.
Proof. intros x y; hnf. decide equality; apply eqType_dec. Defined.

Instance sigLookup_fin : finTypeC (EqType sigLookup).
Proof.
  split with (enum := map sigLookup_Heap enum ++ map sigLookup_HA enum ++ map sigLookup_HClos enum).
  intros. rewrite <- !countSplit.
  destruct x.
*)
       


Definition sigLookup : finType := FinType (EqType (sigHeap + (bool + sigHClos))).
Arguments sigLookup : simpl never.

(* This works as expected *)
Check _ : codable sigLookup Heap.
Check _ : codable sigLookup nat.

Compute encode 1 : list sigHA.
Compute encode 1 : list sigLookup.

Check _ : codable sigLookup (option HClos).
Check _ : codable sigLookup HAd.


Check _ : Retract sigHA sigLookup.
Local Instance Encode_HAd_on_lookup : codable sigLookup HAd := Encode_map Encode_nat (Retract_inl _ _).
Check _ : Retract sigHA sigLookup.


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
else if n = O {
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
  If (Inject (ChangeAlphabet MatchNat (Retract_inl _ _)) [|Fin2|])
     (* [n = S n'] *)
     (Inject (ChangeAlphabet (Nth sigHEnt) _) [|Fin0; Fin1; Fin6; Fin4; Fin5|];;
      If (Inject (ChangeAlphabet (MatchOption sigHEnt) _) [|Fin6|])
         (If (Inject (ChangeAlphabet (MatchOption sigHEnt') _) [|Fin6|])
             (Return
                (Inject (ChangeAlphabet (Snd sigHClos sigHA) _) [|Fin6|];;
                 Inject (ChangeAlphabet (Reset sigHA) _) [|Fin1|];;
                 Inject (ChangeAlphabet (CopyValue sigHA) _) [|Fin6; Fin1|];;
                 Inject (ChangeAlphabet (Reset sigHA) _) [|Fin6|])
                (true, tt))
             (Return (Inject (ChangeAlphabet (Constr_None sigHClos) _) [|Fin3|]) (false, tt)))
         (Return (Inject (ChangeAlphabet (Constr_None sigHClos) _) [|Fin3|]) (false, tt))
     )
     (* [n = O] *)
     (Return
        (Inject (ChangeAlphabet (Nth sigHEnt) _) [|Fin0; Fin1; Fin6; Fin4; Fin5|];;
         If (Inject (ChangeAlphabet (MatchOption sigHEnt) _) [|Fin6|])
            (If (Inject (ChangeAlphabet (MatchOption sigHEnt') _) [|Fin6|])
                (Inject (ChangeAlphabet (MatchPair sigHClos sigHA) _) [|Fin6; Fin3|];;
                 Inject (ChangeAlphabet (Constr_Some sigHClos) _) [|Fin3|])
                (Inject (ChangeAlphabet (Constr_None sigHClos) _) [|Fin3|]))
            (Inject (ChangeAlphabet (Constr_None sigHClos) _) [|Fin3|]))
        (false, tt))
.

Definition Lookup_Step_Rel : Rel (tapes sigLookup^+ 7) (bool*unit * tapes sigLookup^+ 7) :=
  fun tin '(yout, tout) =>
    forall (H: Heap) (a n: nat),
      tin[@Fin0] ≃(Encode_map _ (Retract_inl _ _)) H ->
      tin[@Fin1] ≃(Encode_map _ (Retract_inl _ _)) a ->
      tin[@Fin2] ≃(Encode_map _ (Retract_inl _ _)) n ->
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
    TMSimp; clear_trivial_eqs.
    destruct H; TMSimp; clear_trivial_eqs. (* This takes ***LONG*** *)
    { (* Then branche of [MatchNat]: [n = S n'] *)
      unfold tape_contains in *.
      specialize (H n). spec_assert H.
      { apply contains_translate_tau1. unfold tape_contains in *.
        apply (tape_contains_ext HEncN). cbn. rewrite !List.map_app, !List.map_map. cbn.
        f_equal. 
        - apply map_ext. cbv. intros. f_equal. f_equal. f_equal.

      
      destruct n; cbn in *; destruct H as (H&H'); inv H'.

      specialize (H0 heap a). spec_assert H0.
      { apply contains_translate_tau1. apply (tape_contains_ext HEncH). cbn. now rewrite List.map_map. } spec_assert H0.
      (* { apply contains_translate_tau1. apply (tape_contains_ext HEncA). cbn. rewrite List.map_map. apply map_ext. cbv. give_up.
      } *)
      cbv [Retr_g] in H0.
      unfold tape_contains in H0.


      specialize H0 with (1 := contains_translate_tau1 HEncH).
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