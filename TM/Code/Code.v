Require Import TM.Prelim.
Require Import Coq.Lists.List.

(** * Codable Class **)


Generalizable Variables X Y Z sigma sig tau.


Section Codable.

  Variable (sig: finType).
  Variable (X: Type).

  Class codable :=
    mk_codable
      {
        encode :> X -> list sig
      }.

  Hypothesis codable_X : codable.

End Codable.
Arguments encode { sig } { X } { _ }.

Coercion encode : codable >-> Funclass.


Instance Encode_unit : codable (FinType(EqType(Empty_set))) unit :=
  {|
    encode x := nil
  |}.

Instance Encode_bool : codable (FinType(EqType(bool))) bool:=
  {|
    encode x := [x]
  |}.

Instance Encode_Fin n : codable (FinType(EqType(Fin.t n))) (Fin.t n):=
  {|
    encode i := [i]
  |}.
  

Compute encode true.
(* This works thanks to the coercion above *)
Compute Encode_bool true.
Compute encode tt.
Check encode Fin0.
Compute encode Fin0 : list (Fin.t 10).


(** We restrict mapping of encodings to injective/retractable mappings. *)
Section Encode_map.
  Variable (X : Type).
  Variable (sig tau : finType).
  Hypothesis (code_sig : codable sig X).

  Variable inj : Retract sig tau.

  Global Instance Encode_map : codable tau X | 100 :=
    {
      encode x := map Retr_f (encode x);
    }.
  
End Encode_map.


Section Encode_sum.
  Variable (X Y : Type).
  Variable (sig tau : finType).
  Hypothesis (cX : codable sig X) (cY : codable tau Y).

  Check fun x => encode (x:X) : list (bool+(sig+tau)).
  Check _ : Retract sig (bool + (sig + tau)).

  Global Instance Encode_sum : codable (FinType(EqType(bool+(sig+tau)))) (X+Y) :=
    {|
      encode s := match s with
                  | inl x => inl true  :: encode x
                  | inr y => inl false :: encode y
                  end
    |}.
  
End Encode_sum.

Eval cbn in encode (inl true).


(** If [X] is encodable over [sigX] and [Y] over [sigY]. *)
Section Encode_pair.
  Variable (sig tau: finType) (X Y: Type) (cX : codable sig X) (cY : codable tau Y).

  Global Instance Encode_pair : codable (FinType (EqType (sig+tau))) (X*Y) :=
    {|
      encode '(x,y) := encode x ++ encode y;
    |}.

End Encode_pair.

Section Encode_option.
  Variable (sig: finType) (X: Type) (cX : codable sig X).

  Global Instance Encode_option : codable (FinType(EqType(bool+sig))) (option X) :=
    {|
      encode o := match o with
                  | None => [inl false]
                  | Some x => inl true :: encode x
                  end;
    |}.

End Encode_option.

  

Section Encode_list.
  Variable sig: finType.
  Variable (X : Type) (code_X : codable sig X).

  Fixpoint encode_list (xs : list X) : list (bool + sig) :=
    match xs with
    | nil => [inl false]
    | x :: xs' => inl true :: encode x ++ encode_list xs'
    end.

  Global Instance Encode_list : codable (FinType(EqType(bool+sig))) (list X) :=
    {|
      encode := encode_list;
    |}.
  
End Encode_list.


Section Encode_nat.

  Global Instance Encode_nat : codable (FinType(EqType bool)) nat :=
    {|
      encode n := repeat true n ++ [false];
    |}.

End Encode_nat.


    
(** Test Playground *)

Compute encode (Some true).
Eval cbv in encode None.

Compute encode false.
Compute encode true.

Compute encode (repeat tt 42).
Compute encode 42.

Compute encode (tt, tt).

Compute encode (inl 42).
Compute encode (inr 42).

Compute Encode_pair Encode_nat Encode_nat (1, 2).
Compute encode (1,2).

Compute encode [4;5].
Compute encode (Some 4) ++ encode (Some 5) ++ encode None.

Compute encode ([tt;tt;tt], tt).