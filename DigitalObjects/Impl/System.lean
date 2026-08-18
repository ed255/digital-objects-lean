import DigitalObjects.Spec
import DigitalObjects.Impl.Defs
import DigitalObjects.Impl.TxLib
import DigitalObjects.Impl.Sync

namespace Impl
open Impl (Object StateHeader TxPayload applyTx)

def txCreated (tx : Spec.Tx Object) : List Object :=
  (tx.action.effects tx.objects).filterMap (fun e => match e with
    | .create o => some o
    | .consume _ => none)

def txConsumed (tx : Spec.Tx Object) : List Object :=
  (tx.action.effects tx.objects).filterMap (fun e => match e with
    | .create _ => none
    | .consume o => some o)

def txLive (tx : Spec.Tx Object) : List Object :=
  (txCreated tx).filter (fun o => o ∉ txConsumed tx)

def stateOf (h : List TxPayload) : Option StateHeader :=
  h.foldr (fun tx state? => (state? >>= (fun state => applyTx state tx))) (some genesisState)

def ValidTx (h : List TxPayload) (p : TxPayload) : Prop :=
  ∃ (state state' : StateHeader),
    stateOf h = some state ∧
    applyTx state p = some state'


def impl : Spec.SystemSpec Object TxPayload where
  ValidTx := ValidTx
  specTx p := sorry
  typeOf o := o.type.toSpec
  validTx_effects := sorry
  validTx_mutate := sorry
  validTx_relations_hold := sorry
  validTx_ops_type_match := sorry

end Impl
