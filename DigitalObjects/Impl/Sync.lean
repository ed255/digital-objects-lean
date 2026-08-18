import DigitalObjects.Impl.TxLib
import DigitalObjects.Impl.Defs

namespace Impl

structure TxPayload where
  -- The Tx to be applied
  tx_final : TxLib.Tx
  -- The grounding state
  state_header : StateHeader
  -- The grounding state index
  state_header_index : Nat
  -- The set of nullifiers for this tx (corresponds to consumed objects)
  nullifiers : List Nullifier
  -- The set of new live objects after this tx (corresponds to created objects)
  live : List Object
  -- Proof of TxFinalized
  proof : TxLib.TxFinalized state_header tx_final nullifiers.toFinset live.toFinset

-- Synchronizer procedure
def applyTx (state : StateHeader) (tx : TxPayload) : Option StateHeader :=
  let state_history := state :: state.prior_state_history
  let block_number := state.block_number + 1
  if state_history[tx.state_header_index]? ≠ some tx.state_header then
    none -- state_root not found in recent state root history; rejecting
  else if tx.state_header.block_number < block_number - 300 then
    none -- state_root is too old; rejecting
  else if tx.live ≠ tx.live.eraseDups then
    none -- Duplicate created object within payload; rejecting
  else if tx.live.any (fun o => o ∈ state.created) then
    -- NOTE: All (grounded) inputs to the tx must be consumed (mutated or
    -- deleted).  Otherwise they'll appear in the tx.live and this check will
    -- reject the tx.
    none -- Created object already exists (creation collision); rejecting
  else if tx.nullifiers ≠ tx.nullifiers.eraseDups then
    none -- Duplicate nullifier within payload; rejecting
  else if tx.nullifiers.any (fun n => n ∈ state.nullifiers) then
    none -- Object already consumed (nullifier collision); rejecting
  else
    some
      { block_number := block_number
        created := state.created ++ tx.live
        nullifiers := state.nullifiers ∪ tx.nullifiers.toFinset
        prior_state_history := state_history }

end Impl
