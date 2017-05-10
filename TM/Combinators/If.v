Require Import Match.

Section Composition.

  Variable n : nat.
  Variable sig : finType.

  Variable pM1 : { M1 : mTM sig n & states M1 -> bool}.

  Variable F2 : finType.
  
  Variable pM2 : { M2 : mTM sig n & states M2 -> F2}.
  Variable pM3 : { M3 : mTM sig n & states M3 -> F2}.


  Definition If := MATCH pM1 (fun b => if b then pM2 else pM3).
  Lemma If_sem (R1 : Rel _ _) (R2 : Rel _ (F2 * _)) (R3 : Rel _ (F2 * _)) :
    pM1 ⊫ R1 ->
    pM2 ⊫ R2 ->
    pM3 ⊫ R3 ->
    If ⊫ 
       (R1 |_true) ∘ R2 ∪ (R1 |_false) ∘ R3.
  Proof.
    intros.
    eapply WRealise_monotone.
    - eapply (Match_sem (R1 := R1) (R2 := (fun b => if b then R2 else R3))); eauto.
      now intros [].
    - unfold subrel in *. intuition. cbn in *. destruct H2; cbv in H2; [left | right]; firstorder destruct *; firstorder.
  Qed.

  Lemma If_terminatesIn (R1 : Rel _ (bool * _)) T1 T2 T3 :
    functionalOn T1 R1 ->
    pM1 ⊫ R1 ->
    projT1 pM1 ↓ T1 ->
    projT1 pM2 ↓ T2 ->
    projT1 pM3 ↓ T3 ->
    projT1 If ↓ (fun (t : tapes sig (S n)) (i : nat) =>
            exists (i1 i2 : nat) (b : bool) (y : tapes sig (S n)),
              i > i1 + i2 /\
              (R1 t (b, y) /\ b = true /\ T1 t i1 /\ T2 y i2 \/
                                                  R1 t (b, y) /\ b = false /\ T1 t i1 /\ T3 y i2)).
  Proof.
    intros.
    eapply terminatesIn_monotone.
    - eapply (Match_terminatesIn (R1 := R1) (T := fun b => if b then T2 else T3) ); eauto.
      now destruct f.
    - intros t i (i1 & i2 & b & y & Hi & [(? & ? & ? & ?) | (? & ? & ? & ?)]); cbv -[plus];
        (destruct b; [left|right]; firstorder).
  Qed.

  Lemma If_total (R1 : Rel _ _) (R2 : Rel _ (F2 * _)) (R3 : Rel _ (F2 * _)) k1 k2 k3:
    pM1 ⊨(k1) R1 ->
    pM2 ⊨(k2) R2 ->
    pM3 ⊨(k3) R3 ->
    If ⊨(1 + k1 + Nat.max k2 k3)
       (R1 |_true) ∘ R2 ∪ (R1 |_false) ∘ R3.
  Proof.
    intros.
    eapply RealiseIn_monotone.
    eapply Match_total; eauto.
    - destruct pM1. eassumption.
    - intros. cbn in f. destruct f.
      + eapply RealiseIn_monotone. destruct pM2. eassumption. instantiate (1 := Nat.max k2 k3); firstorder.
        instantiate (1 := fun t => match t with true => R2 | _ => R3 end). reflexivity.
      + eapply RealiseIn_monotone. destruct pM3. eassumption. firstorder. reflexivity.
    - omega.
    - firstorder.
  Qed.
    
End Composition.

(* Section Composition. *)

(*   Variable n : nat. *)
(*   Variable sig : finType. *)

(*   Variable M1 : mTM sig n. *)
(*   Variable M2 : mTM sig n. *)
(*   Variable M3 : mTM sig n. *)

(*   Definition null_action m := repeatVector m (@None sig, N). *)

(*   Lemma tape_move_null_action m tapes : *)
(*     tape_move_multi tapes (null_action m) = tapes. *)
(*   Proof. *)
(*     clear M1 M2. induction tapes; cbn in *; eauto using f_equal. *)
(*   Qed. *)

(*   Definition if_trans (q : states M1) (p : (states M1 + states M2 + states M3) * Vector.t (option sig) (S n)) := *)
(*     let (s,a) := p in *)
(*     match s with *)
(*     | inl (inl s1) => if halt (m := M1) s1 then if Dec (s1 = q) then (inl (inr (start M2)), null_action(S n)) *)
(*                                          else (inr (start M3), null_action (S n)) *)
(*                else let (news1,m) := trans (m := M1) (s1,a) in (inl (inl news1),m) *)
(*     | inl (inr s2)  => let (news2, m) := trans (m := M2) (s2,a) in (inl (inr news2), m) *)
(*     | inr s3 => let (news3, m) := trans (m := M3) (s3,a) in (inr news3, m) *)
(*     end. *)

(*   Definition ifTM (qacc : states M1) : mTM sig n := *)
(*     {| states := FinType (EqType (states M1 + states M2 + states M3)); *)
(*        trans := if_trans qacc; *)
(*        start := inl (inl (start M1)); *)
(*        halt := fun s => *)
(*                   match s with *)
(*                   | inl (inl _) => false *)
(*                   | inl (inr s2) => halt s2  *)
(*                   | inr s3 => halt s3 *)
(*                   end *)
(*     |}. *)

(*   Definition accWRealise (M : mTM sig n) (acc : states M) Rtrue Rfalse := *)
(*     M ⊫(fun x => Decb (x = acc)) (fun x b y => if b then Rtrue x y else Rfalse x y). *)
(*   Arguments accWRealise M acc Rtrue Rfalse : clear implicits. *)

(*   Hint Unfold prcomp prunion ignoreParam. *)

(*   Local Arguments prunion /_ _ _ _ _ _ _. *)
(*   Local Arguments prcomp /_ _ _ _ _ _ _. *)

(*   Lemma sem_if Rtrue Rfalse (F : finType) R2 R3 (f1 : states M1 -> bool) (f2 : states M2 -> F) (f3 : states M3 -> F) acc : *)
(*     M1 ⊫(f1) (fun (x : tapes sig (S n)) (b : finType_CS) (y : tapes sig (S n)) => *)
(*             if b then Rtrue x y else Rfalse x y) -> *)
(*   M2 ⊫(f2) R2 -> *)
(*   M3 ⊫(f3) R3 -> *)
(*   ifTM acc ⊫(fun s : states (ifTM acc) => *)
(*              match s with *)
(*              | inl (inl _) => f2 (start M2) *)
(*              | inl (inr s2) => f2 s2 *)
(*              | inr s3 => f3 s3 *)
(*              end) (⇑Rtrue ◦ R2 ∪ ⇑Rfalse ◦ R3). *)
(*   Proof. *)
(*     intros HR1 HR2 HR3 t i outc HM. *)
(*     unfold WRealise in HR1. *)
(*     cbn. *)

