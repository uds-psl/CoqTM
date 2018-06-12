Require Export ProgrammingTools.
Require Export TM.Code.MatchNat TM.Code.MatchSum TM.Code.MatchFin TM.Code.MatchPair TM.Code.WriteValue.
Require Export TM.LM.Definitions TM.LM.TokTM.


(** * Heap Machine *)


(** ** Alphabets *)

(* See [TokTM] *)



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