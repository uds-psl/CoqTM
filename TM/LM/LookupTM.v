Require Import HeapTM.
Require Import ListTM.


(** ** Lookup *)

Section Lookup.


  Fixpoint lookup (H:Heap) (a:nat) (n:nat) : option HClos :=
    match nth_error H a with
    | Some (Some (g, b)) =>
      match n with
      | 0 => Some g
      | S n' => lookup H b n'
      end
    | _ => None
    end.

  Lemma lookup_eq H a n :
    lookup H a n =
    match nth_error H a with
    | Some (Some (g, b)) =>
      match n with
      | 0 => Some g
      | S n' => lookup H b n'
      end
    | _ => None
    end.
  Proof. destruct n; auto. Qed.

    


  (**
There is no need to save [n], however [H] must be saved. We use the [Nth'] machine, because we don't want to introduce an additional [sigOption sigHEnt] to the alphabet. [Nth'] also doesn't save [a] (which is the parameter of [Nth'] here, not [n]).
[Lookup] will overwrite and reset the variables [a] and [n], but save [H] (which is saved by [Nth']).

Instead of encoding the optional output of the machine with [sigOption sigHClos], our machine will only be specified if the result of [lookup] is [Some]. We can make this assumption because all heap machines we will consider never get stuck. We use the machine [Nth'], which is also only specified, if [nth_error = Some].

We could define [Lookup] over the alphabet [sigHeap], however, in the step machine, we want to read [a] and [n] from a different closure alphabet (sigList sigHClos). [a] is read from an address of a closure and [n] from a variable of this closure, and the output closure will also be copied to this alphabet.
   *)


  Variable sigLookup : finType.
  
  Variable retr_clos_lookup : Retract sigHClos sigLookup.
  Variable retr_heap_lookup : Retract sigHeap sigLookup.


  (**
There are (more than) three possible ways how to encode [nat] on the [Heap] alphabet [sigLookup]:

- 1: as an adress of a closure in an entry
- 2: as the "next" address of an entry
- 3: as a variable of a token inside a closure of the closure input alphabet

[a] is stored in the second way and [n] in the third way.
*)

  (* No 1 *)
  Definition retr_nat_clos_ad : Retract sigNat sigHClos :=
    Retract_sigPair_Y _ _.
  Definition retr_nat_lookup_clos_ad : Retract sigNat sigLookup :=
    ComposeRetract retr_nat_clos_ad retr_clos_lookup.

  (* No 2 *)
  Definition retr_nat_heap_entry : Retract sigNat sigHeap :=
    Retract_sigList_X (Retract_sigOption_X (Retract_sigPair_Y _ (Retract_id _))).
  Local Definition retr_nat_lookup_entry : Retract sigNat sigLookup :=
    ComposeRetract retr_nat_heap_entry retr_heap_lookup.

  (* No 3 *)
  Definition retr_nat_clos_var : Retract sigNat sigHClos :=
    Retract_sigPair_X _ _.
  Definition retr_nat_lookup_clos_var : Retract sigNat sigLookup :=
    ComposeRetract retr_nat_clos_var retr_clos_lookup.

  
  (** Encoding of a closure on the heap alphabet *)
  Definition retr_clos_heap : Retract sigHClos sigHeap := _.
  Definition retr_clos_lookup_heap : Retract sigHClos sigLookup := ComposeRetract retr_clos_heap retr_heap_lookup.

  Definition retr_hent_heap : Retract sigHEnt sigHeap := _.
  Local Definition retr_hent_lookup : Retract sigHEnt sigLookup := ComposeRetract retr_hent_heap retr_heap_lookup.

  Definition retr_hent'_heap : Retract sigHEnt' sigHeap := _.
  Local Definition retr_hent'_lookup : Retract sigHEnt' sigLookup := ComposeRetract retr_hent'_heap retr_heap_lookup.
  
(*
Tapes:
t0: H
t1: a
t2: n
t3: out
t4: internal tape
*)

  Definition Lookup_Step : pTM sigLookup^+ (bool*unit) 5 :=
    Nth' retr_heap_lookup retr_nat_lookup_clos_ad @ [|Fin0; Fin1; Fin4; Fin3|];;
    If (MatchOption sigHEnt'_fin ⇑ retr_hent_lookup @ [|Fin4|])
       (MatchPair sigHClos_fin sigHAd_fin ⇑ retr_hent'_lookup @ [|Fin4; Fin3|];;
        If (MatchNat ⇑ retr_nat_lookup_clos_var @ [|Fin2|])
           (Return (CopyValue _ @ [|Fin4; Fin1|];;
                    Translate retr_nat_lookup_entry retr_nat_lookup_clos_ad @ [|Fin1|];;
                    Reset _ @ [|Fin4|];;
                    Reset _ @ [|Fin3|]) (true, tt))
           (Return (Reset _ @ [|Fin4|];;
                    Reset _ @ [|Fin2|];;
                    Translate retr_clos_lookup_heap retr_clos_lookup @ [|Fin3|]) (false, tt)))
       (Nop default)
  .

  Definition Lookup_Step_Rel : pRel sigLookup^+ (bool*unit) 5 :=
    fun tin '(yout, tout) =>
      forall (H: Heap) (a n: nat) (g : HClos) (b : HAd),
        nth_error H a = Some (Some (g, b)) ->
        tin[@Fin0] ≃ H ->
        tin[@Fin1] ≃(Encode_map Encode_nat retr_nat_lookup_clos_ad ) a ->
        tin[@Fin2] ≃(Encode_map Encode_nat retr_nat_lookup_clos_var) n ->
        isRight tin[@Fin3] -> isRight tin[@Fin4] ->
        match yout, n with
        | (false, tt), O => (* return *)
          tout[@Fin0] ≃ H /\
          isRight tout[@Fin1] /\
          isRight tout[@Fin2] /\
          tout[@Fin3] ≃(Encode_map Encode_HClos retr_clos_lookup) g /\
          isRight tout[@Fin4]
        | (true, tt), S n' => (* continue *)
          tout[@Fin0] ≃ H /\
          tout[@Fin1] ≃(Encode_map Encode_nat retr_nat_lookup_clos_ad ) b /\
          tout[@Fin2] ≃(Encode_map Encode_nat retr_nat_lookup_clos_var) n' /\
          isRight tout[@Fin3] /\
          isRight tout[@Fin4]
        | _, _ => False (* underspecified *)
        end.


  Lemma Lookup_Step_Realise : Lookup_Step ⊨ Lookup_Step_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Lookup_Step. repeat TM_Correct.
      - apply Nth'_Realise.
      - apply CopyValue_Realise with (cX := Encode_map Encode_nat retr_nat_lookup_entry).
      - apply Translate_Realise with (X := nat).
      - apply Reset_Realise with (cX := Encode_map Encode_nat retr_nat_lookup_entry).
      - apply Reset_Realise with (cX := Encode_map Encode_HClos retr_clos_lookup_heap).
      - apply Reset_Realise with (cX := Encode_map Encode_nat retr_nat_lookup_entry).
      - apply Reset_Realise with (cX := Encode_map Encode_nat retr_nat_lookup_clos_var).
      - apply Translate_Realise with (X := HClos).
    }
    {
      intros tin ((yout, ()), tout) H. cbn. intros heap a n g b HNth HEncHeap HEncA HEncN HRight3 HRight4.
      TMSimp. modpon H. destruct H0; TMSimp.
      { (* If of [MatchOption] (sigHEnt') (nth_error = Some) *)
        modpon H0. cbn in *; simpl_surject. modpon H4.
        { instantiate (1 := (g, b)). simpl_surject. apply (tape_contains_ext H0). cbn. now rewrite !List.map_map. }
        cbn in *. destruct H5; TMSimp.
        { (* If of [MatchNat] (n = S n') *)
          modpon H5. destruct n as [ | n']; auto; simpl_surject. inv_pair. modpon H8.
          { instantiate (1 := b). apply (tape_contains_ext H4). cbn. now rewrite !List.map_map. }
          modpon H9. modpon H10. modpon H11.
          { eapply (tape_contains_ext H6). cbn. now rewrite List.map_map. }
          repeat split; auto.
        }
        { (* Else of [MatchNat] *)
          modpon H5. destruct n; auto; simpl_surject. inv_pair. modpon H8.
          { eapply (tape_contains_ext H4). cbn. now rewrite List.map_map. }
          modpon H9. modpon H10.
          { eapply (tape_contains_ext H6). cbn. now rewrite List.map_map. }
          repeat split; auto.
        }
      }
      { (* Then of [MatchOption] (nth_error = None *) modpon H0. cbn in *; auto. }
    }
  Qed.
    

  Definition Lookup := WHILE Lookup_Step.


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


  Definition Lookup_Rel : pRel sigLookup^+ unit 5 :=
    ignoreParam (
        fun tin tout =>
          forall (H: Heap) (a n: nat) (g : HClos),
            lookup H a n = Some g ->
            tin[@Fin0] ≃ H ->
            tin[@Fin1] ≃(Encode_map Encode_nat retr_nat_lookup_clos_ad) a ->
            tin[@Fin2] ≃(Encode_map Encode_nat retr_nat_lookup_clos_var) n ->
            isRight tin[@Fin3] -> isRight tin[@Fin4] ->
            tout[@Fin0] ≃ H /\ (* [H] is saved *)
            isRight tout[@Fin1] /\ (* [a] is discarded *)
            isRight tout[@Fin2] /\ (* [n] is discarded *)
            tout[@Fin3] ≃(Encode_map Encode_HClos retr_clos_lookup) g /\ (* result *)
            isRight tout[@Fin4] (* internal tape *)
      ).


  Lemma Lookup_Realise : Lookup ⊨ Lookup_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Lookup. repeat TM_Correct.
      - apply Lookup_Step_Realise.
    }
    {
      apply WhileInduction; intros; intros heap a n g HLookup HEncHeap HEncA HEncN HRight3 HRight4; TMSimp.
      - rewrite lookup_eq in HLookup. destruct (nth_error heap a) as [ [ (g'&b) | ] | ] eqn:E; cbn in *; try congruence.
        modpon HLastStep. destruct n; auto. inv HLookup. modpon HLastStep. repeat split; auto.
      - rewrite lookup_eq in HLookup. destruct (nth_error heap a) as [ [ (g'&b) | ] | ] eqn:E; cbn in *; try congruence.
        modpon HStar. destruct n; auto. modpon HStar. modpon HLastStep. repeat split; auto.
    }
  Qed.
        
End Lookup.