Require Import TM.Prelim.
Require Import TM.Code.Code.
Require Import Semantics.

(** * Alphabets *)

Inductive ACom : Type := retAT | lamAT | appAT.

Coercion ACom2Com (a : ACom) : Com :=
  match a with
  | retAT => retT
  | lamAT => lamT
  | appAT => appT
  end.


#[export] Instance ACom_eq_dec : eq_dec ACom.
Proof. intros x y; hnf. decide equality. Defined.

#[export] Instance ACom_finType : finTypeC (EqType ACom).
Proof. split with (enum := [retAT; lamAT; appAT]). intros [ | | ]; cbn; reflexivity. Defined.

#[export] Instance ACom_inhab : inhabitedC ACom := ltac:(repeat constructor).

#[export] Instance Encode_ACom : codable ACom ACom := Encode_Finite (FinType(EqType ACom)).


Coercion Com_to_sum (t : Com) : (nat + ACom) :=
  match t with
  | varT x => inl x
  | appT => inr appAT
  | lamT => inr lamAT
  | retT => inr retAT
  end.

Definition sigCom := sigSum sigNat ACom.
Definition sigCom_fin := FinType (EqType sigCom).

#[export] Instance Encode_Com : codable sigCom Com :=
  {|
    encode x := encode (Com_to_sum x)
  |}.

Definition Encode_Com_size (t : Com) : nat :=
  size _ (Com_to_sum t).

Lemma Encode_Com_hasSize (t : Com) :
  size _ t = Encode_Com_size t.
Proof. reflexivity. Qed.


Definition sigHAdd := sigNat.
Definition sigHAdd_fin := FinType(EqType sigHAdd).

Definition sigPro := sigList sigCom.
#[export] Instance Encode_Prog : codable sigPro Pro := _.
Definition sigPro_fin := FinType(EqType sigPro).

Definition sigHClos := sigPair sigHAdd sigPro.
Definition sigHClos_fin := FinType(EqType sigHClos).
#[export] Instance Encode_HClos : codable sigHClos HClos := _.

Definition sigHEntr' := sigPair sigHClos sigHAdd.
#[export] Instance Encode_HEntr' : codable (sigHEntr') (HClos*HAdd) := _.
Definition sigHEntr'_fin := FinType(EqType sigHEntr').

Definition sigHEntr := sigOption sigHEntr'.
#[export] Instance Encode_HEntr : codable (sigHEntr) HEntr := _.
Definition sigHEntr_fin := FinType(EqType sigHEntr).

Definition sigHeap := sigList sigHEntr.
#[export] Instance Encode_Heap : codable (sigHeap) Heap := _.
Definition sigHeap_fin := FinType(EqType sigHeap).
