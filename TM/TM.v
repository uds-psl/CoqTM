(** * Definition of Multitape Turing Machines 
    
    - definitions taken from Asperti, Riciotti "Formalizing Turing Machines" and accompanying Matita foramlisation
*)

Require Export Prelim Relations.
Require Import Vector.

(** Basic stuff that should go somewhere else *)

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
      trans : states * (Vector.t (option sig) (S tapes_no)) -> states * (Vector.t ((option sig) * move) (S tapes_no)); (* the transition function *)
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
  
  Record mconfig (states:finType) (n:nat): Type := mk_mconfig
                                                       {
                                                         cstate : states;
                                                         ctapes : tapes (S n)
                                                      }.

  (** Currently read characters on all tapes *)
  Definition current_chars := fun (n : nat) (tapes : tapes (S n)) => Vector.map current tapes.

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
(*  
  Definition Realise n (M:mTM n) (F : finType) (f : states M -> F) (R : PRel (tapes _) (nat*F)) :=
      forall t, forall i, forall outc, loopM i (initc M t) = Some outc <-> R t (i,f (cstate outc)) (ctapes outc).

  Arguments Realise {n} M {F} f R.*)
  
  Definition WRealise n (F : finType) (pM : { M : mTM n & (states M -> F)}) (R : Rel (tapes _) (F * tapes _)) :=
    forall t i outc, loopM i (initc (projT1 pM) t) = Some outc -> R t ((projT2 pM) (cstate outc), ctapes outc).
  
  Arguments WRealise {n F} pM R.

  Notation "'(' a ';' b ')'" := (existT (fun x => states x -> _) a b).

  (* That's still equivalent to Asperti's definition *)
  Goal forall n (M : mTM n) R, WRealise (M ; fun x => x) (fun x y => R x (snd y) ) <->
      forall t i outc, loopM i (initc M t) = Some outc -> R t (ctapes outc).
  Proof.
    firstorder.
  Qed.
  
  Definition terminatesIn n (M : mTM n) (T: Rel (tapes _) nat) :=
    forall t i , T t i -> exists outc, loopM i (initc M t) = Some outc.

  (* That's still equivalent to Asperti's definition *)
  Goal forall n (M : mTM n) t i, (terminatesIn M (fun t' i' => t=t' /\ i=i')) <->
                          exists outc, loopM i (initc M t) = Some outc.
  Proof.
    intuition. now intros ? ? [-> ->]. 
  Qed.

  
  Notation "M '↓' T" := (terminatesIn M T) (no associativity, at level 30, format "M  '↓'  T").
  Notation "M '⊫' R" := (WRealise M R) (no associativity, at level 30, format "M  '⊫'  R").
  Notation "M '⊫(' f ')' R" := (WRealise (M;f) R) (no associativity, at level 30, format "M  '⊫(' f ')'  R").

  (*
  Notation "M '⊨(' f ')' R" := (Realise M f R) (no associativity, at level 45, format "M  '⊨(' f ')'  R").
*)
  (* Definition rprod A B C (R1 : A -> B -> Prop) (R2 : PRel A C) : PRel A (B * C) := *)
  (*   fun a1 p a2 => let (b,c) := p in R1 a1 b /\ R2 a1 c a2. *)
(*
  Lemma WRealise_to_Realise n (M : mTM n) T (F : finType) (f: states M -> F) R:
    M ⊨(f) rprod T R -> M ↓(T) -> M ⊫(f) R.
  Proof.
    unfold Realise, WRealise, terminatesIn, rprod in *. 
    intuition.  eapply H in H1. firstorder.
  Qed. *)
  
  (** *** Basic Properties *)

  Fact WRealise_monotone n (M:mTM n) (F : finType) (f : states M -> F) (R1 R2 : Rel (tapes _) (F * tapes _)) :
    WRealise (M; f) R1 -> R1 <<=2 R2  -> WRealise (M ; f) R2.
  Proof.
    unfold WRealise. eauto. 
  Qed.

  Fact terminatesIn_monotone n (M : mTM n) (T T': Rel (tapes _) nat)  :
    terminatesIn M T -> T' <<=2 T -> terminatesIn M T'.
  Proof.
    unfold terminatesIn. eauto. 
  Qed.

  Fact terminatesIn_extend n (M : mTM n) (T: Rel (Vector.t (tape) _) nat) :
     terminatesIn M T -> terminatesIn M (fun x i => exists j, j <= i /\ T x i).
  Proof.
    intros H i t (j & ? & H'). now specialize (H _ _ H'). 
  Qed.

  Fact WRealise_changeP n (M:mTM n) (F : finType) (f f' : states M -> F) (R : Rel (tapes _) (F * tapes _)) :
      WRealise (M; f) R -> (forall s, f s = f' s) -> WRealise (M ; f') R.
   Proof.
     intros ? ? ? ? ? ?.
     cbn. rewrite <- H0. firstorder.
   Qed.

  (** *** Properties of total TMs *)

 

  Definition RealiseIn n (F : finType) (pM: {M : mTM n & states M -> F}) (R : Rel (tapes _) (F * tapes _)) k :=
    let (M, f) := pM in
    forall t, exists outc, loopM k (initc M t) = Some outc /\ R t (f (cstate outc), ctapes outc).
  
  Notation "M '⊨(' k ')' R" := (RealiseIn M R k) (no associativity, at level 45, format "M  '⊨(' k ')'  R").
  Notation "M '⊨(' f ',' k ')' R" := (RealiseIn (M; f) R k) (no associativity, at level 45, format "M  '⊨(' f ',' k ')'  R").
    
  Lemma Realise_total n (M : mTM n) (F : finType) (p : states M -> F) R k :
    (M;p) ⊫ R /\ M ↓(fun _ i => i >= k) <-> M ⊨(p,k) R.
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

   Lemma WRealise_total n (M : mTM n) (F : finType) (p : states M -> F) R k :
     M ⊨(p,k) R -> (M;p) ⊫ R.
   Proof.
     intros. now eapply Realise_total.
   Qed.

   Fact RealiseIn_monotone n (M:mTM n) (F : finType) (f : states M -> F) (R1 R2 : Rel (tapes _) (F * tapes _)) k1 k2 :
     RealiseIn (M; f) R1 k1 -> k1 <= k2 -> R1 <<=2 R2  -> RealiseIn (M ; f) R2 k2.
   Proof.
     unfold RealiseIn. intuition. destruct (H t) as (outc & ?). exists outc.
     split.
     - unfold loopM. eapply loop_ge; eauto. intuition.
     - intuition.
   Qed.

   
   Fact RealiseIn_changeP n (M:mTM n) (F : finType) (f f' : states M -> F) (R : Rel (tapes _) (F * tapes _)) k :
      RealiseIn (M; f) R k -> (forall s, f s = f' s) -> RealiseIn (M ; f') R k.
   Proof.
     firstorder congruence.
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

Notation "'(' a ';' b ')'" := (existT (fun x => states x -> _) a b).
Notation "M '↓' T" := (terminatesIn M T) (no associativity, at level 60, format "M  '↓'  T").
Notation "M '⊫' R" := (WRealise M R) (no associativity, at level 60, format "M  '⊫'  R").
Notation "M '⊫(' f ')' R" := ((M;f) ⊫ R) (no associativity, at level 60, format "M  '⊫(' f ')'  R").
Notation "M '⊨(' k ')' R" := (RealiseIn M R k) (no associativity, at level 45, format "M  '⊨(' k ')'  R").
Notation "M '⊨(' f ',' k ')' R" := (RealiseIn (M; f) R k) (no associativity, at level 45, format "M  '⊨(' f ',' k ')'  R").
