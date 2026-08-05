import DigitalObjects.Impl.Types

namespace TxLib
open Impl.Types (Object ObjectType Chain Event)

-- TxLib uses hash chains to roll a sequence of values and then unroll it.
-- Assuming secure cryptographic hashes and the random oracle model, we can
-- assume a one to one mapping between a hash chain and a list.  For simplicity
-- we use a list here.

-- NOTE: Object stable identifier (statements using "stable_identifier") is out
-- of the scope for now.  We may model it in the future.

-- From digital-objects txlib (podlang code):
-- // Insert: chain = H(prev, H({}, new)). The `type` arg pins the
-- // inserted object's type field so ReplayInsert can dispatch the
-- // guard without re-extracting it. The DictInsert clause stamps
-- // `new.stable_identifier = commitment(initial)`: `initial` is the
-- // pre-identity object dict the action constructed (script-driven
-- // DictUpdates land on `initial`), and `new` is the materialized
-- // post-identity dict the tx records in its `live` set. Exposing
-- // `initial` as a public arg lets the calling action predicate
-- // share its body wildcard with both the script's DictUpdate chain
-- // and TxInsert's identity-derivation clause.
-- TxInsert(chain, prev_chain, initial, new, type, private: event_hash) = AND(
--   DictContains(new, "type", type)
--   DictInsert(initial, "stable_identifier", initial, new)
--   Hash({}, new, event_hash)
--   Hash(prev_chain, event_hash, chain)
-- )
def TxInsert (chain prev_chain : Chain) (new : Object) (type : ObjectType) :=
  ∃ event : Event,
  new.type = type ∧
  event = .insert new ∧
  chain = {prev_chain with events := event :: prev_chain.events}

-- From digital-objects txlib (podlang code):
-- // Mutate: chain = H(prev, H(old, new)). The shared `type` arg pins
-- // both old and new to the same type, enforcing type preservation
-- // implicitly (no separate Equal needed). The Equal clause pins
-- // old.stable_identifier == new.stable_identifier so the stable
-- // identifier set by TxInsert survives every mutation.
-- TxMutate(chain, prev_chain, new, old, type, private: event_hash) = AND(
--   DictContains(new, "type", type)
--   DictContains(old, "type", type)
--   Equal(old.stable_identifier, new.stable_identifier)
--   Hash(old, new, event_hash)
--   Hash(prev_chain, event_hash, chain)
-- )
def TxMutate (chain prev_chain : Chain) (new old : Object) (type : ObjectType) :=
  ∃ event : Event,
  new.type = type ∧
  old.type = type ∧
  event = .mutate old new ∧
  chain = {prev_chain with events := event :: prev_chain.events}

-- From digital-objects txlib (podlang code):
-- // Delete: chain = H(prev, H(old, {})). The `type` arg pins the
-- // deleted object's type field for guard dispatch.
-- TxDelete(chain, prev_chain, old, type, private: event_hash) = AND(
--   DictContains(old, "type", type)
--   Hash(old, {}, event_hash)
--   Hash(prev_chain, event_hash, chain)
-- )
def TxDelete (chain prev_chain : Chain) (old : Object) (type : ObjectType) :=
  ∃ event : Event,
  old.type = type ∧
  event = .delete old ∧
  chain = {prev_chain with events := event :: prev_chain.events}

end TxLib
