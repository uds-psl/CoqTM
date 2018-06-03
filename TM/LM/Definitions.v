Require Import TM.Code.CodeTM.

(** ** Definitions for the heap machine *)
Inductive Tok := varT (n :nat) | appT | lamT | retT.
Definition Pro := list Tok.
Definition HAd : Type := nat.
Definition HClos : Type := Pro * HAd.
Definition HEnt : Type := option (HClos * HAd).
Definition Heap : Type := list HEnt.
