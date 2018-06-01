(** * Definition of Multi-Tape Turing Machines 
 *)
(** Some definitions inspired from Asperti, Riciotti "Formalizing Turing Machines" and accompanying Matita foramlisation  *)

Require Export TM.Prelim TM.Relations.
Require Import Shared.Vectors.Vectors.
(*
Require Import Vector.
*)

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
  
  
  (** Definition of tape movements *)

  Definition tape_move_right' ls a rs :=
    match rs with
    | nil => rightof a ls
    | r::rs' => midtape (a::ls) r rs'
    end.

  Definition tape_move_right :=
    fun (t : tape) =>
      match t with
      | niltape => niltape
      | rightof _ _ =>t
      | leftof a rs =>midtape  [ ] a rs
      | midtape ls a rs => tape_move_right' ls a rs
      end.


  Definition tape_move_left' ls a rs :=
    match ls with
    | nil => leftof a rs
    | l::ls' => midtape ls' l (a::rs)
    end.
  
  Definition tape_move_left :=
    fun (t : tape) =>
      match t with 
      | niltape => niltape 
      | leftof _ _ => t
      | rightof a ls => midtape ls a [ ]
      | midtape ls a rs => tape_move_left' ls a rs
      end. 

  (*
  (* This shouldn't reduce with [cbn], because we don't know how [l] looks like. *)
  Eval cbn in (tape_move_left (midtape _ _ _)).
  (* This should reduce. *)
  Eval cbn in (tape_move_left (midtape (_::_) _ _)).
  *)

  
  Definition tape_move (t : tape) (m : move) :=
    match m with
    | R => tape_move_right t
    | L => tape_move_left t | N => t
    end.

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

  Lemma tape_move_right_left (t : tape) (s : sig) :
    current t = Some s ->
    tape_move_left (tape_move_right t) = t.
  Proof.
    intros H1. destruct t; cbn in *; inv H1; auto; destruct l; auto; destruct l0; auto.
  Qed.

  Lemma tape_move_left_right (t : tape) (s : sig) :
    current t = Some s ->
    tape_move_right (tape_move_left t) = t.
  Proof.
    intros H1. destruct t; cbn in *; inv H1; auto; destruct l; auto; destruct l0; auto.
  Qed.

  (** Writing on the tape *)

  Definition tape_write (t : tape) (s : option sig) :=
    match s with 
    | None => t
    | Some s0 => midtape (left t) s0 (right t)
    end.

End Fix_Sigma.

(* Destruct a vector of tapes of known size *)
Ltac destruct_tapes := unfold tapes in *; destruct_vector.

(* Simplification Database for tapes and vectors *)
Create HintDb tape.
Create HintDb vector.

Tactic Notation "simpl_tape" :=  autorewrite with tape vector.
Tactic Notation "simpl_tape" "in" hyp_list(H) :=  autorewrite with tape vector in H.
Tactic Notation "simpl_tape" "in" "*" := autorewrite with tape vector in *.

Tactic Notation "simpl_vector" :=  autorewrite with vector.
Tactic Notation "simpl_vector" "in" hyp_list(H) :=  autorewrite with vector in H.
Tactic Notation "simpl_vector" "in" "*" := autorewrite with vector in *.

Hint Rewrite tapeToList_move : tape.
Hint Rewrite tapeToList_move_R : tape.
Hint Rewrite tapeToList_move_L : tape.
Hint Rewrite tape_move_right_left using eauto : tape.
Hint Rewrite tape_move_left_right using eauto : tape.

Lemma nth_map' (A B : Type) (f : A -> B) (n : nat) (v : Vector.t A n) (k : Fin.t n) :
  (VectorDef.map f v)[@k] = f v[@k].
Proof. erewrite VectorSpec.nth_map; eauto. Qed.

Lemma nth_map2' (A B C : Type) (f : A -> B -> C) (n : nat) (v1 : Vector.t A n) (v2 : Vector.t B n) (k : Fin.t n) :
  (VectorDef.map2 f v1 v2)[@k] = f v1[@k] v2[@k].
Proof. erewrite VectorSpec.nth_map2; eauto. Qed.

Hint Rewrite @nth_map' : vector.
Hint Rewrite @nth_map2' : vector.
Hint Rewrite @nth_tabulate : vector.



(* Set Notation scopes for tapes *)
Arguments tapes (sig % type) (n % nat).



Section MirrorTape.
  Variable (n : nat) (sig : finType).

  Definition mirror_tape (t : tape sig) : tape sig :=
    match t with
    | niltape _ => niltape _
    | leftof r rs => rightof r rs
    | rightof l ls => leftof l ls
    | midtape ls m rs => midtape rs m ls
    end.

  Lemma mirror_tape_left (t : tape sig) :
    left (mirror_tape t) = right t.
  Proof. now destruct t. Qed.

  Lemma mirror_tape_right (t : tape sig) :
    right (mirror_tape t) = left t.
  Proof. now destruct t. Qed.

  Lemma mirror_tape_current (t : tape sig) :
    current (mirror_tape t) = current t.
  Proof. now destruct t. Qed.

  Lemma mirror_tape_involution (t : tape sig) :
    mirror_tape (mirror_tape t) = t.
  Proof. destruct t; cbn; congruence. Qed.

  Lemma mirror_tape_injective (t1 t2 : tape sig) :
    mirror_tape t1 = mirror_tape t2 ->
    t1 = t2.
  Proof. destruct t1, t2; intros H; cbn in *; congruence. Qed.


  Lemma mirror_tape_move_left (t : tape sig) :
    mirror_tape (tape_move_left t) = tape_move_right (mirror_tape t).
  Proof. destruct t; cbn; auto. destruct l; cbn; auto. Qed.

  Lemma mirror_tape_move_right (t : tape sig) :
    mirror_tape (tape_move_right t) = tape_move_left (mirror_tape t).
  Proof. destruct t; cbn; auto. destruct l0; cbn; auto. Qed.


  Lemma mirror_tape_inv_midtape t r1 r2 x :
    mirror_tape t = midtape r1 x r2 -> t = midtape r2 x r1.
  Proof. intros. destruct t; cbn in *; congruence. Qed.

  Lemma mirror_tape_inv_leftof t rs x :
    mirror_tape t = leftof rs x -> t = rightof rs x.
  Proof. intros. destruct t; cbn in *; congruence. Qed.

  Lemma mirror_tape_inv_rightof t ls x :
    mirror_tape t = rightof ls x -> t = leftof ls x.
  Proof. intros. destruct t; cbn in *; congruence. Qed.

  Lemma mirror_tape_inv_niltape t :
    mirror_tape t = niltape _  -> t = niltape _.
  Proof. intros. destruct t; cbn in *; congruence. Qed.

  Lemma mirror_tape_inv_midtape' t r1 r2 x :
    midtape r1 x r2 = mirror_tape t -> t = midtape r2 x r1.
  Proof. intros. destruct t; cbn in *; congruence. Qed.

  Lemma mirror_tape_inv_leftof' t rs x :
    leftof rs x = mirror_tape t -> t = rightof rs x.
  Proof. intros. destruct t; cbn in *; congruence. Qed.

  Lemma mirror_tape_inv_rightof' t ls x :
    rightof ls x = mirror_tape t -> t = leftof ls x.
  Proof. intros. destruct t; cbn in *; congruence. Qed.

  Lemma mirror_tape_inv_niltape' t :
    niltape _ = mirror_tape t -> t = niltape _.
  Proof. intros. destruct t; cbn in *; congruence. Qed.


  Definition mirror_tapes (t : tapes sig n) : tapes sig n := Vector.map mirror_tape t.

  Lemma mirror_tapes_involution (t : tapes sig n) :
    mirror_tapes (mirror_tapes t) = t.
  Proof.
    unfold mirror_tapes. apply Vector.eq_nth_iff. intros ? ? ->.
    erewrite !Vector.nth_map; eauto. apply mirror_tape_involution.
  Qed.

  Lemma mirror_tapes_injective (t1 t2 : tapes sig n) :
    mirror_tapes t1 = mirror_tapes t2 ->
    t1 = t2.
  Proof.
    intros H. unfold mirror_tapes in *. apply Vector.eq_nth_iff. intros ? ? ->.
    eapply Vector.eq_nth_iff with (p1 := p2) in H; eauto.
    erewrite !Vector.nth_map in H; eauto. now apply mirror_tape_injective.
  Qed.
  
  Definition mirror_move (D : move) : move := match D with | N => N | L => R | R => L end.

  Lemma mirror_move_involution (D : move) : mirror_move (mirror_move D) = D.
  Proof. now destruct D. Qed.

  Lemma mirror_tapes_nth (tapes : tapes sig n) (k : Fin.t n) :
    (mirror_tapes tapes)[@k] = mirror_tape (tapes[@k]).
  Proof. intros. eapply VectorSpec.nth_map; eauto. Qed.

End MirrorTape.

Arguments mirror_tapes : simpl never.
Hint Unfold mirror_tapes : tape.

Hint Rewrite mirror_tape_left : tape.
Hint Rewrite mirror_tape_right : tape.
Hint Rewrite mirror_tape_current : tape.
Hint Rewrite mirror_tape_involution : tape.
Hint Rewrite mirror_tape_move_left : tape.
Hint Rewrite mirror_tape_move_right : tape.
Hint Rewrite mirror_tapes_involution : tape.
Hint Rewrite mirror_tapes_nth using eauto : tape.


Section Tape_Local.

  Variable sig : finType.

  Definition tape_local (t : tape sig) : list sig :=
    match t with
    | niltape _ => []
    | leftof a l => []
    | rightof _ _ => []
    | midtape _ a l => a :: l
    end.

  Definition tape_local_l (t : tape sig) : list sig :=
    match t with
    | niltape _ => []
    | leftof a l => []
    | rightof _ _ => []
    | midtape r a l => a :: r
    end.

  Lemma tape_local_mirror (t : tape sig) :
    tape_local_l (mirror_tape t) = tape_local t.
  Proof. destruct t; cbn; auto. Qed.

  Lemma tape_local_mirror' (t : tape sig) :
    tape_local (mirror_tape t) = tape_local_l t.
  Proof. destruct t; cbn; auto. Qed.
    
  Lemma tape_local_current_cons (x : sig) (xs : list sig) (t : tape sig) :
    tape_local t = x :: xs -> current t = Some x.
  Proof. destruct t eqn:E; cbn; congruence. Qed.

  Lemma tape_local_l_current_cons (x : sig) (xs : list sig) (t : tape sig) :
    tape_local t = x :: xs -> current t = Some x.
  Proof. destruct t eqn:E; cbn; congruence. Qed.

  Lemma tape_local_right (x : sig) (xs : list sig) (t : tape sig) :
    tape_local t = x :: xs -> right t = xs.
  Proof. destruct t eqn:E; cbn; congruence. Qed.

  Lemma tape_local_l_left (x : sig) (xs : list sig) (t : tape sig) :
    tape_local_l t = x :: xs -> left t = xs.
  Proof. destruct t eqn:E; cbn; congruence. Qed.

  Lemma tape_local_cons_iff (t : tape sig) (x : sig) (xs : list sig) :
    tape_local t = x :: xs <-> current t = Some x /\ right t = xs.
  Proof.
    split; intros H.
    - destruct t; cbn in *; inv H. eauto.
    - destruct t; cbn in *; inv H; inv H0. eauto.
  Qed.

  Lemma tape_local_l_cons_iff (t : tape sig) (x : sig) (xs : list sig) :
    tape_local_l t = x :: xs <-> current t = Some x /\ left t = xs.
  Proof.
    split; intros H.
    - destruct t; cbn in *; inv H. eauto.
    - destruct t; cbn in *; inv H; inv H0. eauto.
  Qed.

  
  Lemma tape_local_nil (t : tape sig) :
    tape_local t = [] <-> current t = None.
  Proof.
    destruct t; cbn; intuition; auto; congruence.
  Qed.

  Lemma tape_local_move_right (t : tape sig) (x : sig) (xs : list sig) :
    tape_local t = x :: xs -> tape_local (tape_move_right t) = xs.
  Proof.
    intro H. destruct t eqn:E; cbn in *; try congruence.
    inv H. destruct xs; cbn; auto.
  Qed.

  Lemma tape_local_l_move_left (t : tape sig) (x : sig) (xs : list sig) :
    tape_local_l t = x :: xs -> tape_local_l (tape_move_left t) = xs.
  Proof.
    intro H. destruct t eqn:E; cbn in *; try congruence.
    inv H. destruct xs; cbn; auto.
  Qed.
  
  Lemma tape_left_move_right (t : tape sig) (x : sig) :
    current t = Some x -> left (tape_move_right t) = x :: left t.
  Proof. intros H. destruct t; cbn in *; try congruence. inv H. destruct l0; cbn; reflexivity. Qed.

  Lemma tape_right_move_left (t : tape sig) (x : sig) :
    current t = Some x -> right (tape_move_left t) = x :: right t.
  Proof. intros H. destruct t; cbn in *; try congruence. inv H. destruct l; cbn; reflexivity. Qed.

  Lemma midtape_tape_local_cons t r2 x :
    tape_local t = x :: r2 <-> t = midtape (left t) x r2.
  Proof.
    split.
    - intros H1. destruct t; cbn in *; congruence.
    - intros H1. destruct t; cbn in *; inv H1. auto.
  Qed.
  
  Lemma midtape_tape_local_cons_left t r1 r2 x :
    left t = r1 /\ tape_local t = x :: r2 <-> t = midtape r1 x r2.
  Proof. rewrite midtape_tape_local_cons. intuition subst; cbn; auto. Qed.

  
  Lemma midtape_tape_local_l_cons t r1 x :
    tape_local_l t = x :: r1 <-> t = midtape r1 x (right t).
  Proof.
    split.
    - intros H1. destruct t; cbn in *; congruence.
    - intros H1. destruct t; cbn in *; inv H1. auto.
  Qed.
  
  Lemma midtape_tape_local_l_cons_right t r1 r2 x :
    tape_local_l t = x :: r1 /\ right t = r2 <-> t = midtape r1 x r2.
  Proof. rewrite midtape_tape_local_l_cons. intuition subst; cbn; auto. Qed.

End Tape_Local.

Hint Rewrite tape_local_mirror  : tape.
Hint Rewrite tape_local_mirror' : tape.
Hint Rewrite tape_local_current_cons using auto : tape.
Hint Rewrite tape_local_l_current_cons using auto : tape.
Hint Rewrite tape_local_right        using auto : tape.
Hint Rewrite tape_local_l_left        using auto : tape.
Hint Rewrite tape_left_move_right    using auto : tape.
Hint Rewrite tape_right_move_left    using auto : tape.


(* Apply a function to each symbol on the tape *)
Section MapTape.
  Variable sig tau : finType.
  Variable g : tau -> sig.

  Definition mapTape : tape tau -> tape sig.
  Proof.
    destruct 1 eqn:E1.
    - apply niltape.
    - apply leftof.  apply (g e). apply (List.map g l).
    - apply rightof. apply (g e). apply (List.map g l).
    - apply midtape. apply (List.map g l). apply (g e). apply (List.map g l0).
  Defined.

  Definition mapTapes {n : nat} : Vector.t (tape tau) n -> Vector.t (tape sig) n := Vector.map mapTape.

  (* Correctness of mapTape *)

  Lemma mapTape_current t :
    current (mapTape t) =
    match (current t) with
    | Some m => Some (g m)
    | None => None
    end.
  Proof. destruct t; cbn; reflexivity. Qed.

  Lemma mapTape_left t :
    left (mapTape t) = List.map g (left t).
  Proof. destruct t; cbn; reflexivity. Qed.

  Lemma mapTape_right t :
    right (mapTape t) = List.map g (right t).
  Proof. destruct t; cbn; reflexivity. Qed.

  Lemma mapTape_move_left t :
    tape_move_left (mapTape t) = mapTape (tape_move_left t).
  Proof. destruct t; cbn; auto. destruct l; cbn; auto. Qed.

  Lemma mapTape_move_right t :
    tape_move_right (mapTape t) = mapTape (tape_move_right t).
  Proof. destruct t; cbn; auto. destruct l0; cbn; auto. Qed.

  Lemma mapTape_inv_niltap t :
    mapTape t = niltape _ ->
    t = niltape _.
  Proof. intros. destruct t; inv H. repeat econstructor. Qed.

  Lemma mapTape_inv_rightof t l ls :
    mapTape t = rightof l ls ->
    exists l' ls', t = rightof l' ls' /\
              l = g l' /\
              ls = map g ls'.
  Proof. intros. destruct t; inv H. repeat econstructor. Qed.

  Lemma mapTape_inv_leftof t r rs :
    mapTape t = leftof r rs ->
    exists r' rs', t = leftof r' rs' /\
              r = g r' /\
              rs = map g rs'.
  Proof. intros. destruct t; inv H. repeat econstructor. Qed.

  Lemma mapTape_inv_midtape t ls m rs :
    mapTape t = midtape ls m rs ->
    exists ls' m' rs', t = midtape ls' m' rs' /\
                  ls = map g ls' /\
                  m = g m' /\
                  rs = map g rs'.
  Proof. intros. destruct t; inv H. repeat econstructor. Qed.

  (*
  Lemma mapTapes_nth {n : nat} (ts : tapes tau n) (k : Fin.t n) :
    (mapTapes ts)[@k] = mapTape (ts[@k]).
  Proof. unfold mapTapes. eapply VectorSpec.nth_map; eauto. Qed.
   *)

End MapTape.

(* Rewriting Hints *)

Hint Rewrite nth_map' : tape.
Hint Rewrite mapTape_current    : tape.
Hint Rewrite mapTape_left       : tape.
Hint Rewrite mapTape_right      : tape.
Hint Rewrite mapTape_move_left  : tape.
Hint Rewrite mapTape_move_right : tape.
(*
Hint Rewrite mapTapes_nth       : tape.
*)
Hint Unfold mapTapes : tape.


Lemma mapTape_mapTape (sig tau gamma : finType) (f : sig -> tau) (g : tau -> gamma) (t : tape sig) :
  mapTape g (mapTape f t) = mapTape (fun x => g (f x)) t.
Proof. destruct t; cbn; auto; simpl_tape; now rewrite !map_map. Qed.

Lemma mapTape_ext (sig tau : finType) (f g : sig -> tau) (t : tape sig) :
  (forall a, f a = g a) -> mapTape f t = mapTape g t.
Proof. intros H. destruct t; cbn; auto; simpl_tape; rewrite H; f_equal; eapply map_ext; eauto. Qed.

Lemma mapTape_id (sig : finType) (t : tape sig) :
  mapTape (fun x => x) t = t.
Proof. destruct t; cbn; auto; f_equal; apply map_id. Qed.
Hint Rewrite mapTape_mapTape : tape.
Hint Rewrite mapTape_id : tape.


Lemma mapTape_local (sig tau : finType) (f : sig -> tau) t :
  tape_local (mapTape f t) = List.map f (tape_local t).
Proof. destruct t; cbn; reflexivity. Qed.
Hint Rewrite mapTape_local : tape.



(** Lemmas about [tape_move_left'] and [tape_move_right'] *)
Section MatchTapes.
  Variable sig : finType.

  Lemma tape_right_move_left' ls (x : sig) rs :
    right (tape_move_left' ls x rs) = x :: rs.
  Proof. destruct ls; cbn; reflexivity. Qed.

  Lemma tape_left_move_right' ls (x : sig) rs :
    left (tape_move_right' ls x rs) = x :: ls.
  Proof. destruct rs; cbn; reflexivity. Qed.

  Lemma tape_right_move_right' ls (x : sig) rs :
    left (tape_move_left' ls x rs) = tl ls.
  Proof. now destruct ls; cbn. Qed.

  Lemma tape_left_move_left' ls (x : sig) rs :
    right (tape_move_right' ls x rs) = tl rs.
  Proof. now destruct rs; cbn. Qed.
  
  Lemma tape_local_move_right' rs (x : sig) ls :
    tape_local (tape_move_right' rs x ls) = ls.
  Proof. destruct ls; cbn; reflexivity. Qed.

  Lemma tape_local_l_move_left' rs (x : sig) ls :
    tape_local_l (tape_move_left' rs x ls) = rs.
  Proof. destruct rs; cbn; reflexivity. Qed.

  
End MatchTapes.

Hint Rewrite tape_right_move_left' : tape.
Hint Rewrite tape_left_move_right' : tape.
Hint Rewrite tape_right_move_right' : tape.
Hint Rewrite tape_left_move_left' : tape.
Hint Rewrite tape_local_move_right' : tape.
Hint Rewrite tape_local_l_move_left' : tape.






(** ** Definition of Multi-Tape Turing Machines *)
Section Semantics.

  Variable sig : finType.
  

  Record mTM (n:nat) : Type :=
    {
      states : finType; (* states of the TM *)
      trans : states * (Vector.t (option sig) n) -> states * (Vector.t ((option sig) * move) n); (* the transition function *)
      start: states; (* the start state *)
      halt : states -> bool (* decidable subset of halting states *)
    }.

  (** Partitioned Multi-Tape Turing Machines *)
  Definition pTM (F: finType) (n:nat) := { M : mTM n & states M -> F }.
  

  (** A single step of the machine *)
  
  Definition tape_move_mono (t : tape sig) (mv : option sig * move) :=
    tape_move (tape_write t (fst mv)) (snd mv).

  (** One step on each tape *)
  
  Definition tape_move_multi (n : nat) (ts : tapes sig n) (actions : Vector.t (option sig * move) n) :=
    Vector.map2 tape_move_mono ts actions.

  (** *** Configurations of TMs *)
  
  Record mconfig (states:finType) (n:nat): Type :=
    mk_mconfig
      {
        cstate : states;
        ctapes : tapes sig n
      }.

  (** Currently read characters on all tapes *)
  Definition current_chars (n : nat) (tapes : tapes sig n) := Vector.map (@current _) tapes.


  (** *** Machine execution *)
  
  Definition step n (M:mTM n) (c:mconfig (states M) n) :=
    let (news,actions) := trans (cstate c, current_chars  (ctapes c)) in 
    mk_mconfig news (tape_move_multi (ctapes c) actions).

  (** Run the machine i steps until it halts *)
  Definition loopM n (M : mTM n) (i : nat) cin :=
    loop i (@step n M) (fun c => halt (cstate c)) cin.
  
  (** Initial configuration *)  
  Definition initc n (M : mTM n) tapes :=
    mk_mconfig (n := n) (@start n M) tapes.


  (** *** Realisation *)

  Notation "'(' a ';' b ')'" := (existT (fun x => states x -> _) a b).

  (** Parametrised relations *)
  Definition pRel (F: finType) (n : nat) := Rel (tapes sig n) (F * tapes sig n).

  (** A (partitioned) machine [M] realises a (parametrised) relation [R], if: for every tape vectors [t], if [M] with [t] terminates in a configuration [c], then [R (t), (projT2 M (cstate c), ctapes c)], which means that the pair of the input tape vectors, the partition where the machine terminated, and the output tape, must be in the relation [R]. *)
  
  Definition Realise n F (pM : pTM n F) (R : pRel n F) :=
    forall t i outc, loopM i (initc (projT1 pM) t) = Some outc -> R t (projT2 pM (cstate outc), ctapes outc).

  Notation "M '⊨' R" := (Realise M R) (no associativity, at level 30, format "M  '⊨'  R").

  Lemma Realise_monotone n (F : finType) (pM : pTM F n) R1 R2 :
    pM ⊨ R1 -> R1 <<=2 R2 -> pM ⊨ R2.
  Proof. firstorder. Qed.


  (** *** Termination/Runtime *)

  (** A machine is said to "terminate in" a relation [T : Rel (tapes sig n) nat], if for every pair of input tape vectors [t] and step numbers [i], there exists an output configuration [cout] that [M] reaches from [t] in [i] steps. *)

  Definition tRel n := Rel (tapes sig n) nat.

  Definition TerminatesIn {n : nat} (M : mTM n) (T : tRel n) :=
    forall tin k, T tin k -> exists conf, loopM k (initc M tin) = Some conf.
  

  Arguments TerminatesIn { _ } _.
  Notation "M ↓ T" := (TerminatesIn M T) (no associativity, at level 60, format "M  '↓'  T").

  Lemma TerminatesIn_monotone {n : nat} (M : mTM n) (T1 T2 : tRel n) :
    M ↓ T1 -> (T2 <<=2 T1) -> M ↓ T2.
  Proof.
    intros H1 H2. firstorder.
  Qed.

  Lemma TerminatesIn_extend {n : nat} (M : mTM n) (T1 T2 : tRel n) :
    M ↓ T1 -> (forall tin k1, T2 tin k1 -> exists k2, k2 <= k1 /\ T1 tin k2) -> M ↓ T2.
  Proof.
    intros H1 H2. hnf. intros tin k1 Hk.
    specialize (H2 tin k1 Hk) as (k3&Hk3&Hk3').
    hnf in H1. specialize (H1 tin k3 Hk3') as (oconf&HLoop).
    exists oconf. eapply loop_ge; eauto.
  Qed.


  (** Realisation and termination in constant time *)
  Definition RealiseIn n (F : finType) (pM : pTM F n) (R : pRel F n) (k : nat) :=
    forall input, exists outc, loopM k (initc (projT1 pM) input) = Some outc /\ R input ((projT2 pM (cstate outc)), ctapes outc).
  Notation "M '⊨c(' k ')' R" := (RealiseIn M R k) (no associativity, at level 45, format "M  '⊨c(' k ')'  R").

  Fact RealiseIn_monotone n (F : finType) (pM : pTM F n) (R1 R2 : pRel F n) k1 k2 :
    pM ⊨c(k1) R1 -> k1 <= k2 -> R1 <<=2 R2  -> pM ⊨c(k2) R2.
  Proof.
    unfold RealiseIn. intros H1 H2 H3 input.
    specialize (H1 input) as (outc & H1). exists outc.
    split.
    - unfold loopM. eapply loop_ge; eauto. intuition.
    - intuition.
  Qed.

  Fact RealiseIn_monotone' n (F : finType) (pM : pTM F n) (R1 : pRel F n) k1 k2 :
    pM ⊨c(k1) R1 -> k1 <= k2 -> pM ⊨c(k2) R1.
  Proof.
    intros H1 H2. eapply RealiseIn_monotone. eapply H1. assumption. firstorder.
  Qed.

  Fact RealiseIn_split n (F : finType) (pM : pTM F n) R1 R2 (k : nat) :
    pM ⊨c(k) R1 /\ pM ⊨c(k) R2 <-> pM ⊨c(k) R1 ∩ R2.
  Proof.
    split; swap 1 2; [ intros H | intros (H1&H2)]; repeat intros ?. hnf; firstorder eauto.
    specialize (H1 input) as (outc &H1&H1'). specialize (H2 input) as (outc2&H2&H2').
    pose proof loop_functional H1 H2 as <-. exists outc. split; hnf; eauto.
  Qed.
  
  Fact Realise_total n (F : finType) (pM : { M : mTM n & states M -> F }) R k :
    pM ⊨ R /\ projT1 pM ↓ (fun _ i => k <= i) <-> pM ⊨c(k) R.
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

  Fact RealiseIn_Realise n (F : finType) (pM : pTM F n) R k :
    pM ⊨c(k) R -> pM ⊨ R.
  Proof. now intros (?&?) % Realise_total. Qed.

  Fact RealiseIn_terminatesIn n (F : finType) (pM : { M : mTM n & states M -> F }) R k :
    pM ⊨c(k) R -> projT1 pM ↓ (fun tin l => k <= l). 
  Proof.
    intros HRel. hnf. intros tin l HSteps. hnf in HRel. specialize (HRel tin) as (outc&HLoop&Rloop).
    exists outc. eapply loop_ge; eauto.
  Qed.
  
  Fact Realise_strengthen n (F : finType) (pM : pTM F n) R1 R2 :
    Realise pM R2 -> Realise pM R1 -> Realise pM (R1 ∩ R2).
  Proof.
    intros HwR HR t. firstorder.
  Qed.


  (** *** Canonical relations *)

  Section CanonicalRelation1.
    Variable (n : nat).
    Variable (F : finType).
    Variable (pM : { M : mTM n & states  M -> F }).

    Definition R_canonical : pRel F n :=
      fun t1 '(y, t2) =>
        exists outc k, loopM (M := projT1 pM) k (initc (projT1 pM) t1) = Some outc /\
                  ctapes outc = t2 /\ projT2 pM (cstate outc) = y.

    Lemma Realise_R_mTM :
      pM ⊨ R_canonical.
    Proof. hnf. firstorder eauto. Qed.

    Lemma R_canonical_functional : functional R_canonical.
    Proof.
      hnf. intros x (y1&z1) (y2&z2) (c1&k1&H1&<-&H1') (c2&k2&H2&<-&H2').
      pose proof loop_functional H1 H2 as ->. congruence.
    Qed.

  End CanonicalRelation1.

  Section CanonicalRelation2.
    Variable (n : nat).
    Variable (M : mTM n).

    Definition T_canonical : tRel n :=
      fun t k => exists outc, loopM (M := M) k (initc M t) = Some outc.

    Lemma T_canonical_TerminatesIn :
      M ↓ T_canonical.
    Proof. firstorder. Qed.

  End CanonicalRelation2.


End Semantics.




Arguments TerminatesIn {_} {_} _.

Notation "'(' a ';' b ')'" := (existT (fun x => states x -> _) a b).
Notation "M '⊨' R" := (Realise M R) (no associativity, at level 60, format "M  '⊨'  R").
Notation "M '⊨c(' k ')' R" := (RealiseIn M R k) (no associativity, at level 45, format "M  '⊨c(' k ')'  R").
Notation "M '↓' t" := (TerminatesIn M t) (no associativity, at level 60, format "M  '↓'  t").


Arguments current_chars : simpl never.
Hint Unfold current_chars : tape.


(* Auxiliary function to actually execute a machine *)
Definition execTM (sig : finType) (n : nat) (M : mTM sig n) (steps : nat) (tapes : tapes sig n) :=
  option_map (@ctapes _ _ _) (loopM steps (initc M tapes)).

Definition execTM_p (sig : finType) (n : nat) (F : finType) (pM : { M : mTM sig n & states M -> F }) (steps : nat) (tapes : tapes sig n) :=
  option_map (fun x => (ctapes x, projT2 pM (cstate x))) (loopM steps (initc (projT1 pM) tapes)).



(** ** Automatisation of the generation of relations *)

(* Create the smpl tactic databases *)
Smpl Create TM_Correct.

(* This tactics apply exactly one tactic from the corresponding hint database *)
Ltac TM_Correct := smpl TM_Correct.

Smpl Add progress eauto : TM_Correct.

(*
(* TODO: get rid of that *)
Smpl Add rewrite <- sigT_eta : TM_Correct.
*)

