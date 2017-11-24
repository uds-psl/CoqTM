(** * Definition of Multitape Turing Machines 
    
    - definitions taken from Asperti, Riciotti "Formalizing Turing Machines" and accompanying Matita foramlisation
 *)

Require Export Prelim Relations.
Require Import Vector.

Section Fix_Sigma.

  Variable sig : finType.

  (** ** Definition of the tape *)
  
  (** A tape is essentially a triple 〈left,current,right〉 where however the current 
symbol could be missing. This may happen for three different reasons: both tapes 
are empty; we are on the left extremity of a non-empty tape (left overflow), or 
we are on the right extremity of a non-empty tape (right overflow). *)
  
  Inductive tape : Type :=
  | niltape : tape
  | leftof : sig -> list sig -> tape
  | rightof : sig -> list sig -> tape
  | midtape : list sig -> sig -> list sig -> tape.

  Definition tapes n := Vector.t tape n.

  Definition tapeToList (t : tape) : list sig :=
    match t with
    | niltape => []
    | leftof s r => s :: r
    | rightof s l => List.rev (s :: l)
    | midtape l c r => (List.rev l) ++ [c] ++ r 
    end.

  Definition sizeOfTape t := |tapeToList t|.

  Definition sizeOfmTapes n (v : tapes n) :=
    Vector.fold_left max 0 (Vector.map sizeOfTape v).
  
  Definition current :=
    fun (t : tape) =>
      match t with
      | midtape _ c _ => Some c
      | _ => None
      end.

  Definition left :=
    fun (t : tape) =>
      match t with
      | niltape => []
      | leftof _ _ => []
      | rightof s l => s :: l
      | midtape l _ _ => l
      end.

  Definition right :=
    fun (t : tape) =>
      match t with
      | niltape => []
      | leftof s r => s :: r
      | rightof _ _ => []
      | midtape _ _ r => r
      end.

  Definition mk_tape ls c rs :=
    match c with
    | Some c => midtape ls c rs
    | None => match ls with
             | List.nil => match rs with
                          | List.nil => niltape
                          | r :: rs => leftof r rs
                          end
             | l :: ls => rightof l ls
             end
    end.

  (** ** Definition of moves *)
  
  Inductive move : Type := L : move | R : move | N : move.

  Global Instance move_eq_dec : eq_dec move.
  Proof.
    intros. hnf. decide equality.
  Defined.

  Global Instance move_finC : finTypeC (EqType move).
  Proof.
    apply (FinTypeC (enum := [L; R; N])).
    intros []; now cbv.
  Qed.
  
  (** ** Definition of Multitape Turing Machines *)

  Record mTM (tapes_no:nat) : Type :=
    {
      states : finType; (* states of the TM *)
      trans : states * (Vector.t (option sig) tapes_no) -> states * (Vector.t ((option sig) * move) tapes_no); (* the transition function *)
      start: states; (* the start state *)
      halt : states -> bool (* decidable subset of halting states *)
    }.

  (** Definition of tape movements *)

  Definition tape_move_right :=
    fun (t : tape) =>
      match t with
        niltape => niltape
      | rightof _ _ =>t
      | leftof a rs =>midtape  [ ] a rs
      | midtape ls a rs =>
        match rs with
          []  => rightof  a ls
        | a0 :: rs0 => midtape (a::ls) a0 rs0
        end
      end.

  Definition tape_move_left :=
    fun (t : tape) =>
      match t with 
        niltape => niltape 
      | leftof _ _ => t
      | rightof a ls => midtape ls a [ ]
      | midtape ls a rs => 
        match ls with 
          [] => leftof a rs
        | a0 :: ls0 => midtape ls0 a0 (a::rs)
        end
      end. 

  Definition tape_move := fun (t : tape) (m : move) =>
                            match m with  R => tape_move_right t | L => tape_move_left t | N => t end.

  (* Rewriting Lemmas *)

  Lemma tapeToList_move (t : tape) (D : move) :
    tapeToList (tape_move t D) = tapeToList t.
  Proof.
    destruct t, D; cbn; auto.
    - revert e l0. induction l; intros; cbn in *; simpl_list; auto.
    - revert e l. induction l0; intros; cbn in *; simpl_list; auto.
  Qed.

  Lemma tapeToList_move_R (t : tape) :
    tapeToList (tape_move_right t) = tapeToList t.
  Proof. apply (tapeToList_move t R). Qed.

  Lemma tapeToList_move_L (t : tape) :
    tapeToList (tape_move_left t) = tapeToList t.
  Proof. apply (tapeToList_move t L). Qed.



  (** Writing on the tape *)

  Definition tape_write := fun (t : tape) (s : option sig) =>
                             match s with 
                               None => t
                             | Some s0 => midtape (left t) s0 (right t)
                             end.

  (** A single step of the machine *)
  
  Definition tape_move_mono := fun (t : tape) (mv : option sig * move) =>
                                 tape_move (tape_write t (fst mv)) (snd mv).

  (** One step on each tape *)
  
  Definition tape_move_multi := fun (n : nat) (ts : tapes n) (actions : Vector.t (option sig * move) n)=>
                                  map2 tape_move_mono ts actions.

  (** ** Configurations of TMs *)
  
  Record mconfig (states:finType) (n:nat): Type :=
    mk_mconfig
      {
        cstate : states;
        ctapes : tapes n
      }.

  (** Currently read characters on all tapes *)
  Definition current_chars := fun (n : nat) (tapes : tapes n) => Vector.map current tapes.

  (** ** Machine execution *)
  
  Definition step :=
    fun n (M:mTM n) (c:mconfig (states M) n) => 
      let (news,actions) := trans (cstate c, current_chars  (ctapes c)) in 
      mk_mconfig news (tape_move_multi (ctapes c) actions).

  (** Run the machine i steps until it halts *)
  Definition loopM := fun n (M :mTM n) (i : nat) cin =>
                        loop i (@step n M) (fun c => halt (cstate c)) cin.
  
  (** Initial configuration *)  
  Definition initc := fun n (M : mTM n) tapes =>
                        mk_mconfig (n := n) (@start n M) tapes.

  (** ** Realisation of machines *)

  Notation "'(' a ';' b ')'" := (existT (fun x => states x -> _) a b).
  
  Definition WRealise n (F : finType) (pM : { M : mTM n & (states M -> F)}) (R : Rel (tapes _) (F * tapes _)) :=
    forall t i outc, loopM i (initc (projT1 pM) t) = Some outc -> R t ((projT2 pM) (cstate outc), ctapes outc).
  Arguments WRealise {n F} pM R.

  Notation "M '⊫' R" := (WRealise M R) (no associativity, at level 30, format "M  '⊫'  R").
  Notation "M '⊫(' p ')' R" := (WRealise (M; p) R) (no associativity, at level 30, format "M  '⊫(' p ')'  R").

  (* That's still equivalent to Asperti's definition *)
  Goal forall n (M : mTM n) R, WRealise (M ; fun x => x) (fun x y => R x (snd y) ) <->
                          forall t i outc, loopM i (initc M t) = Some outc -> R t (ctapes outc).
  Proof.
    firstorder.
  Qed.

  (** *** Basic Properties *)

  Fact WRealise_monotone n (F : finType) (pM : { M : mTM n & states M -> F }) (R1 R2 : Rel (tapes _) (F * tapes _)) :
    pM ⊫ R1 -> R1 <<=2 R2 -> pM ⊫ R2.
  Proof.
    unfold WRealise. eauto. 
  Qed.

  Fact WRealise_changeP n (M:mTM n) (F : finType) (f f' : states M -> F) (R : Rel (tapes _) (F * tapes _)) :
    WRealise (M; f) R -> (forall s, f s = f' s) -> WRealise (M ; f') R.
  Proof.
    intros ? ? ? ? ? ?. cbn. rewrite <- H0. firstorder.
  Qed.

  (** *** Properties of total TMs *)

  Definition Realise {n : nat} {F : finType} (pM : { M : mTM n & (states M -> F) }) (R : Rel (tapes _) (F * tapes _)) :=
    forall (input : tapes n),
    exists outc k, loopM k (initc (projT1 pM) input) = Some outc /\
              R input ((projT2 pM (cstate outc)), ctapes outc).
  Notation "M '⊨' R" := (Realise M R) (no associativity, at level 45, format "M  '⊨'  R").
  Notation "M '⊨(' p ')' R" := (Realise (M;p) R) (no associativity, at level 45, format "M  '⊨(' p ')'  R").

  Lemma Realise_monotone n (F : finType) (pM : { M : mTM n & (states M -> F) }) R1 R2 :
    pM ⊨ R1 -> R1 <<=2 R2 -> pM ⊨ R2.
  Proof.
    intros. hnf in *. firstorder.
  Qed.

  Lemma Realise_WRealise n (F : finType) (pM : { M : mTM n & (states M -> F) }) R :
    pM ⊨ R -> pM ⊫ R.
  Proof.
    intros H. intros input k outc H1.
    pose proof (H input) as (outc'&k'&H2&H3).
    now rewrite (loop_functional H1 H2) in *.
  Qed.

  Definition TerminatesIn {n : nat} (M : mTM n) (T : Rel (tapes n) nat) :=
    forall tin k, T tin k -> exists conf, loopM k (initc M tin) = Some conf.
  Arguments TerminatesIn { _ } _.
  Notation "M ↓ T" := (TerminatesIn M T) (no associativity, at level 60, format "M  '↓'  T").

  Lemma TerminatesIn_monotone {n : nat} (M : mTM n) (T1 T2 : Rel (tapes _) _) :
    M ↓ T1 -> (forall x y, T2 x y -> T1 x y) -> M ↓ T2.
  Proof.
    intros H1 H2. firstorder.
  Qed.

  Lemma WRealise_to_Realise n (F : finType) (pM : { M : mTM n & (states M -> F) }) R T :
    projT1 pM ↓ T ->
    (forall t, exists k, T t k) ->
    pM ⊫ R -> pM ⊨ R.
  Proof.
    intros H1 H2 H3. intros input. hnf in *. specialize (H2 input) as (k&Hk). specialize (H1 _ _ Hk) as (oconf&HL). eauto.
  Qed.

  Definition RealiseIn n (F : finType) (pM : { M : mTM n & (states M -> F) }) R (k : nat) :=
    forall input, exists outc, loopM k (initc (projT1 pM) input) = Some outc /\ R input ((projT2 pM (cstate outc)), ctapes outc).
  Notation "M '⊨c(' k ')' R" := (RealiseIn M R k) (no associativity, at level 45, format "M  '⊨c(' k ')'  R").
  Notation "M '⊨c(' p ',' k ')' R" := (RealiseIn (M; p) R k) (no associativity, at level 45, format "M  '⊨c(' p ',' k ')'  R").

  Lemma RealiseIn_Realise n (F : finType) (pM : { M : mTM n & (states M -> F) }) R (k : nat) :
    pM ⊨c(k) R -> pM ⊨ R.
  Proof. firstorder. Qed.

  Fact RealiseIn_monotone n (F : finType) (pM : { M : mTM n & (states M -> F) }) (R1 R2 : Rel (tapes _) (F * tapes _)) k1 k2 :
    pM ⊨c(k1) R1 -> k1 <= k2 -> R1 <<=2 R2  -> pM ⊨c(k2) R2.
  Proof.
    unfold RealiseIn. intros H1 H2 H3 input.
    specialize (H1 input) as (outc & H1). exists outc.
    split.
    - unfold loopM. eapply loop_ge; eauto. intuition.
    - intuition.
  Qed.

  Fact RealiseIn_monotone' n (F : finType) (pM : { M : mTM n & (states M -> F) }) (R1 : Rel (tapes _) (F * tapes _)) k1 k2 :
    pM ⊨c(k1) R1 -> k1 <= k2 -> pM ⊨c(k2) R1.
  Proof.
    intros H1 H2. eapply RealiseIn_monotone. eapply H1. assumption. firstorder.
  Qed.
  
  Fact Realise_total n (F : finType) (pM : { M : mTM n & states M -> F }) R k :
    pM ⊫ R /\ projT1 pM ↓ (fun _ i => i >= k) <-> pM ⊨c(k) R.
  Proof.
    split.
    - intros (HR & Ht) t. edestruct (Ht t k). cbn; omega. eauto.
    - intros H.
      split.
      + intros t i cout Hc.
        destruct (H t) as (? & ? & ?).
        cutrewrite (cout = x).
        eassumption.
        eapply loop_functional; eauto.
      + intros t i Hi.
        edestruct (H t) as (? & ? & ?). 
        exists x. eapply loop_ge; eauto.
  Qed.

  
  Fact RealiseIn_changeP n (M:mTM n) (F : finType) (f f' : states M -> F) (R : Rel (tapes _) (F * tapes _)) k :
    RealiseIn (M; f) R k -> (forall s, f s = f' s) -> RealiseIn (M ; f') R k.
  Proof.
    destruct M. cbn in *. unfold RealiseIn. cbn. firstorder congruence.
  Qed.

  Fact RealiseIn_strengthen n (M : mTM n) (F : finType) (f : states M -> F) (R1 R2 : Rel (tapes _) (F * tapes _)) k :
    WRealise (M; f) R2 -> RealiseIn (M ; f) R1 k -> RealiseIn (M ; f) (R1 ∩ R2) k.
  Proof.
    intros HwR HR t.  destruct (HR t) as (outc & ?). exists outc. firstorder.
  Qed.

  (** ** Canonical relations *)
(*
  Definition R_mTM :=
    fun n (M : mTM n) q t1 t2 =>
      exists i outc, loopM (M := M) i (mk_mconfig q t1) = Some outc /\ t2 = (ctapes outc).

  Lemma Wrealise_R_mTM n (M:mTM  n) :
    M ⊫ R_mTM (@start n M).
  Proof.
    firstorder.
  Qed.
  
  Lemma R_mTM_to_R n (M:mTM n) R t1 t2 :
    M ⊫ R -> R_mTM (@start n M) t1 t2 -> R t1 t2.
  Proof.
    firstorder subst. eauto.
  Qed.
 *)
End Fix_Sigma.

(* Arguments Realise {sig} {n} M {F} f R : clear implicits. *)
(* Arguments WRealise {sig n F} pM R : clear implicits. *)
(* Arguments RealiseIn {sig n F} pM R k : clear implicits. *)
Arguments TerminatesIn {_} {_} _.

Notation "'(' a ';' b ')'" := (existT (fun x => states x -> _) a b).
Notation "M '⊫' R" := (WRealise M R) (no associativity, at level 60, format "M  '⊫'  R").
Notation "M '⊫(' f ')' R" := ((M;f) ⊫ R) (no associativity, at level 60, format "M  '⊫(' f ')'  R").
Notation "M '⊨' R" := (Realise M R) (no associativity, at level 60, format "M  '⊨'  R").
Notation "M '⊨(' f ')' R" := ((M;f) ⊫ R) (no associativity, at level 60, format "M  '⊨(' f ')'  R").
Notation "M '⊨c(' k ')' R" := (RealiseIn M R k) (no associativity, at level 45, format "M  '⊨c(' k ')'  R").
Notation "M '⊨c(' f ',' k ')' R" := (RealiseIn (M; f) R k) (no associativity, at level 45, format "M  '⊨c(' f ',' k ')'  R").
Notation "M '↓' t" := (TerminatesIn M t) (no associativity, at level 60, format "M  '↓'  t").

(* Destruct a vector of tapes of known size *)
Ltac destruct_tapes := unfold tapes in *; destruct_vector.

(* Simplification Database for tapes *)
Create HintDb tape.

Tactic Notation "simpl_tape" := autorewrite with tape.
Tactic Notation "simpl_tape" "in" hyp(H) := autorewrite with tape in H.
Tactic Notation "simpl_tape" "in" "*" := autorewrite with tape in *.

Hint Rewrite tapeToList_move : tape.
Hint Rewrite tapeToList_move_R : tape.
Hint Rewrite tapeToList_move_L : tape.