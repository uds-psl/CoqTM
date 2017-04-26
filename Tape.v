Require Export Base.
Require Export Datatypes.
Require Export FinSet.

Import FinSet.FinSet.

Module Tape.

  Section Tape.

    (* The alphabet *)
    Variable alphabet : finSet.

    Implicit Types (n i : nat).
    Implicit Types (r l m x : alphabet).
    Implicit Types (rs ls xs ys : list alphabet).

    Inductive tape : Type :=
    | Empty : tape
    | Middle ls m rs : tape
    | LeftOf  (n : nat) r rs : tape
    | RightOf (n : nat) l ls : tape.

    Implicit Types (s t tape u : tape).
             
    Inductive move : Type :=
    | Left | Right | Stay.

    Implicit Types (mv : move).

    Definition leftOf tape :=
      match tape with
      | Empty => nil
      | Middle ls m rs => ls
      | RightOf i l ls => l :: ls
      | LeftOf i r rs  => nil
      end.

    Definition rightOf tape :=
      match tape with
      | Empty => nil
      | Middle ls m rs => rs
      | RightOf i l ls => nil
      | LeftOf i r rs => r :: rs
      end.

    Definition symbolAt tape :=
      match tape with
      | Middle ls m rs => Some m
      | _ => None
      end.

    Definition content tape :=
      match tape with
      | Empty => nil
      | Middle ls m rs => rev ls ++ [m] ++ rs
      | RightOf i l ls => rev (l :: ls)
      | LeftOf i r rs => r :: rs
      end.
    
    
    Definition moveRight tape :=
      match tape with
      | Empty => Empty
      | Middle ls m nil => RightOf 0 m ls
      | Middle ls m (r::rs) => Middle (m::ls) r rs
      | RightOf i l ls => RightOf (S i) l ls
      | LeftOf 0 r rs => Middle nil r rs
      | LeftOf (S i) r rs => LeftOf i r rs
      end.

    Definition moveLeft tape :=
      match tape with
      | Empty => Empty
      | Middle nil m rs => LeftOf 0 m rs
      | Middle (l::ls) m rs => Middle ls l (m::rs)
      | RightOf 0 l ls => Middle ls l nil
      | RightOf (S i) l ls => RightOf i l ls
      | LeftOf i r rs => LeftOf (S i) r rs
      end.

    Definition moveTape tape mv :=
      match mv with
      | Left => moveLeft tape
      | Right => moveRight tape
      | Stay => tape
      end.

    Definition write tape (s : option alphabet) :=
      match s with
      | None => tape
      | Some x => Middle (leftOf tape) x (rightOf tape)
      end.
    
    

    (** Band Content is invariant on moves *)

    Lemma contentInvariantLeft tape :
      content tape = content (moveLeft tape).
    Proof.
      destruct tape; cbn; auto.
      - destruct ls; cbn; auto. rewrite <- app_assoc. auto.
      - destruct n; cbn; auto. 
    Qed.

    Lemma contentInvariantRight tape :
      content tape = content (moveRight tape).
    Proof.
      destruct tape; cbn; auto.
      - destruct rs; cbn; auto. rewrite <- app_assoc. auto.
      - destruct n; cbn; auto. 
    Qed.

    Theorem contentInvariantMove tape mv :
      content tape = content (moveTape tape mv).
    Proof.
      destruct mv.
      - apply contentInvariantLeft.
      - apply contentInvariantRight.
      - reflexivity.
    Qed.


    (** Write does not change leftOf and rightOf *)

    Lemma write_left a tape :
      leftOf (write tape (Some a)) = leftOf tape.
    Proof. cbn. reflexivity. Qed.

    Lemma write_right a tape :
      rightOf (write tape (Some a)) = rightOf tape.
    Proof. cbn. reflexivity. Qed.

    (** Write Symbol -> Read Symbol -> Same symbol *)
    Lemma write_read a tape :
      symbolAt (write tape (Some a)) = Some a.
    Proof. cbn. reflexivity. Qed.

    (** Read Symbol -> Write Symbol -> Same Tape *)
    Lemma read_write tape :
      write tape (symbolAt tape) = tape.
    Proof.
      destruct (symbolAt tape) as [a|] eqn:H.
      - destruct tape eqn:H'; cbn in *; congruence.
      - reflexivity.
    Qed.
    
  End Tape.
End Tape.