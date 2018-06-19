Require Import TM.Prelim.
Require Import TM.Code.Code.
Require Import Semantics.

(** * Alphabets *)

(* See [TokTM] *)

Inductive ATok : Type := retAT | lamAT | appAT.

Coercion ATok2Tok (a : ATok) : Tok :=
  match a with
  | retAT => retT
  | lamAT => lamT
  | appAT => appT
  end.


Instance ATok_eq_dec : eq_dec ATok.
Proof. intros x y; hnf. decide equality. Defined.

Instance ATok_finType : finTypeC (EqType ATok).
Proof. split with (enum := [retAT; lamAT; appAT]). intros [ | | ]; cbn; reflexivity. Defined.

Instance ATok_inhab : inhabitedC ATok := ltac:(repeat constructor).

Instance Encode_ATok : codable ATok ATok := Encode_Finite (FinType(EqType ATok)).


Coercion Tok_to_sum (t : Tok) : (nat + ATok) :=
  match t with
  | varT x => inl x
  | appT => inr appAT
  | lamT => inr lamAT
  | retT => inr retAT
  end.

Definition sigTok := sigSum sigNat ATok.
Definition sigTok_fin := FinType (EqType sigTok).

Instance Encode_Tok : codable sigTok Tok :=
  {|
    encode x := encode (Tok_to_sum x)
  |}.

Definition Encode_Tok_size (t : Tok) : nat :=
  size _ (Tok_to_sum t).

Lemma Encode_Tok_hasSize (t : Tok) :
  size _ t = Encode_Tok_size t.
Proof. reflexivity. Qed.


Definition sigHAd := sigNat.
Definition sigHAd_fin := FinType(EqType sigHAd).

Definition sigPro := sigList sigTok.
Instance Encode_Prog : codable sigPro Pro := _.
Definition sigPro_fin := FinType(EqType sigPro).

Definition sigHClos := sigPair sigHAd sigPro.
Definition sigHClos_fin := FinType(EqType sigHClos).
Instance Encode_HClos : codable sigHClos HClos := _.

Definition sigHEnt' := sigPair sigHClos sigHAd.
Instance Encode_HEnt' : codable (sigHEnt') (HClos*HAd) := _.
Definition sigHEnt'_fin := FinType(EqType sigHEnt').

Definition sigHEnt := sigOption sigHEnt'.
Instance Encode_HEnt : codable (sigHEnt) HEnt := _.
Definition sigHEnt_fin := FinType(EqType sigHEnt).

Definition sigHeap := sigList sigHEnt.
Instance Encode_Heap : codable (sigHeap) Heap := _.
Definition sigHeap_fin := FinType(EqType sigHeap).
