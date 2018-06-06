Require Export TM.Code.CodeTM TM.Code.Copy.
Require Export TM.Code.MatchNat TM.Code.MatchSum TM.Code.MatchFin TM.Code.MatchPair TM.Code.WriteValue.
Require Export TM.Code.ChangeAlphabet TM.LiftMN TM.LiftSigmaTau.
Require Export TM.Basic.Mono.
Require Export TM.Code.ListTM. (* [Nth] *)
Require Export TM.LM.Definitions TM.LM.TokTM.


(** * Heap Machine *)


(** ** Alphabets *)

(* See [TokTM] *)
Arguments sigTok : simpl never.

Definition sigHAd := FinType (EqType sigNat).
Arguments sigHAd : simpl never.

Definition sigPro := FinType (EqType (sigList sigTok)).
Arguments sigPro : simpl never.
Instance Encode_Prog : codable sigPro Pro := _.

Definition sigHClos := FinType (EqType (sigPair sigPro sigHAd)).
Arguments sigHClos : simpl never.
Instance Encode_HClos : codable sigHClos HClos := _.

Definition sigHEnt' := FinType (EqType (sigPair sigHClos sigHAd)).
Arguments sigHEnt' : simpl never.
Instance Encode_HEnt' : codable sigHEnt' (HClos*HAd) := _.

Definition sigHEnt := FinType (EqType (sigOption sigHEnt')).
Arguments sigHEnt : simpl never.
Instance Encode_HEnt : codable sigHEnt HEnt := _.

Definition sigHeap := FinType (EqType (sigList sigHEnt)).
Arguments sigHeap : simpl never.
Instance Encode_Heap : codable sigHeap Heap := _.