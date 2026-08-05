import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Relation
import DigitalObjects.Impl.Types
import DigitalObjects.Impl.TxLib.Events

namespace TxLib
open Types (Object ObjectType Nullifier Chain)

def ArrayContains {α : Type} (array : List α) (index : Nat) (element : α) : Prop :=
  array[index]? = some element

def SetInsert {α : Type} [DecidableEq α] (set : Finset α) (element : α) (set' : Finset α) : Prop :=
  element ∉ set ∧ set' = insert element set

def SetDelete {α : Type} [DecidableEq α] (set : Finset α) (element : α) (set' : Finset α) : Prop :=
  element ∈ set ∧ set' = set.erase element

structure Tx where
  live : Finset Object
  nullifiers : Finset Nullifier
  chain_start : Chain
  chain_end : Chain

structure StateHeader where
  block_number : Nat
  created : List Object
  nullifiers : Finset Nullifier
  prior_state_history : List StateHeader

-- The automatic derivation of DecidableEq doesn't support the nested
-- recursion through `List StateHeader`, so we define it manually (same
-- pattern as `Impl.Event`/`Impl.Action`).
mutual
  def StateHeader.decEq : (a b : StateHeader) → Decidable (a = b)
    | ⟨n1, c1, nf1, ph1⟩, ⟨n2, c2, nf2, ph2⟩ =>
      have := StateHeader.decEqList ph1 ph2
      decidable_of_iff (n1 = n2 ∧ c1 = c2 ∧ nf1 = nf2 ∧ ph1 = ph2) (by simp)
  termination_by a _ => sizeOf a

  def StateHeader.decEqList : (as bs : List StateHeader) → Decidable (as = bs)
    | [], [] => .isTrue rfl
    | [], _ :: _ => .isFalse nofun
    | _ :: _, [] => .isFalse nofun
    | a :: as, b :: bs =>
      have := StateHeader.decEq a b
      have := StateHeader.decEqList as bs
      decidable_of_iff (a = b ∧ as = bs) (by simp)
  termination_by as _ => sizeOf as
end

instance : DecidableEq StateHeader := StateHeader.decEq

-- Auxiliary types
structure Ins where
  new : Object
  new_live : Finset Object
structure Pair where
  old : Object
  new : Object

-- // ========================================================
-- // Replay: Helpers
-- // ========================================================

-- // Standalone nullifier derivation: H(H(obj, obj.key), "txlib-nullifier-v1").
-- // In practice we inline this into ReplayNullify, but it's useful to have it
-- // for third-party code that needs to compute nullifiers outside of replay.
-- Nullify(nullifier, obj, private: obj_key_hash) = AND(
--   Hash(obj, obj.key, obj_key_hash)
--   Hash(obj_key_hash, "txlib-nullifier-v1", nullifier)
-- )
inductive Nullify : (nullifier : Nullifier) → (obj : Object) → Prop where
  | mk (nullifier : Nullifier) (obj : Object)
    -- statements
    (h : nullifier = obj.nullify) :
    Nullify nullifier obj

-- // ========================================================
-- // Replay: Actions
-- // ========================================================
-- //
-- // An action is a contiguous segment of the hash chain that groups
-- // related events (e.g. "mine a stone" = mutate pick + insert stone).
-- // Actions nest: a parent action can contain sub-actions.
-- //
-- // Replaying an action:
-- //   1. Write the action's chain range into tx as chain_start/chain_end
-- //      (so guard dispatch knows which action scope to match).
-- //   2. Replay the action's contents (events and sub-actions).
-- //   3. Copy inner live/nullifier changes back to the outer tx
-- //      (restoring the parent's chain_start/chain_end automatically,
-- //      since after_tx derives from before_tx, not inner_tx).

mutual
  -- // Set chain_start/chain_end in tx, replay contents, copy live/nullifiers
  -- // back to outer tx (which restores the parent's chain_start/chain_end).
  -- ReplayAction(before_tx, after_tx, before_chain, after_chain,
  --     private: scope_mid, inner_tx, end_tx, mid) = AND(
  --   DictUpdate(before_tx, "chain_start", before_chain, scope_mid)
  --   DictUpdate(scope_mid, "chain_end", after_chain, inner_tx)
  --   ReplayContents(inner_tx, end_tx, before_chain, after_chain)
  --   DictUpdate(before_tx, "live", end_tx.live, mid)
  --   DictUpdate(mid, "nullifiers", end_tx.nullifiers, after_tx)
  -- )
  inductive ReplayAction : (before_tx after_tx : Tx) → (before_chain after_chain : Chain) → Prop where
    | mk (before_tx after_tx : Tx) (before_chain after_chain : Chain)
      -- private
      (scope_mid inner_tx end_tx mid : Tx)
      -- statements
      (h1 : scope_mid = {before_tx with chain_start := before_chain})
      (h2 : inner_tx = {scope_mid with chain_end := after_chain})
      (h3 : ReplayContents inner_tx end_tx before_chain after_chain)
      (h4 : mid = {before_tx with live := end_tx.live})
      (h5 : after_tx = {mid with nullifiers := end_tx.nullifiers}) :
      ReplayAction before_tx after_tx before_chain after_chain

  -- // Top-level walker: every event at the transaction's top level is
  -- // required by construction to be an action (the prover API never
  -- // emits bare events outside an action scope). Dispatching directly
  -- // to ReplayAction here skips the ReplayElement layer that would
  -- // otherwise be needed to discriminate between event variants.
  -- // ReplayContents is still used *within* an action, where inserts,
  -- // mutates, deletes, and sub-actions can all appear. Empty top-level
  -- // transactions are forbidden by TxBuilder, so there is no Done leaf.
  -- //
  -- // `ReplayActionInsert` is a K=1 fast path: when the single top-level
  -- // action's body is a lone Insert, the entire transaction proves in
  -- // 2 statements from this OR (ReplayActions -> ReplayActionInsert),
  -- // bypassing ReplayAction/ReplayContents/ReplayElement/ReplayInsert
  -- // (5 statements). "Mining" actions that just produce one object hit
  -- // this path.
  -- ReplayActions(before_tx, after_tx, before_chain, after_chain) = OR(
  --   ReplayAction(before_tx, after_tx, before_chain, after_chain)
  --   ReplayActionsStep(before_tx, after_tx, before_chain, after_chain)
  --   ReplayActionInsert(before_tx, after_tx, before_chain, after_chain)
  -- )
  inductive ReplayActions : (before_tx after_tx : Tx) → (before_chain after_chain : Chain) → Prop where
    | action (before_tx after_tx : Tx) (before_chain after_chain : Chain)
      (h : ReplayAction before_tx after_tx before_chain after_chain) :
      ReplayActions before_tx after_tx before_chain after_chain
    | actions_step (before_tx after_tx : Tx) (before_chain after_chain : Chain)
      (h : ReplayActionsStep before_tx after_tx before_chain after_chain) :
      ReplayActions before_tx after_tx before_chain after_chain
    | action_insert (before_tx after_tx : Tx) (before_chain after_chain : Chain)
      (h : ReplayActionInsert before_tx after_tx before_chain after_chain) :
      ReplayActions before_tx after_tx before_chain after_chain

  -- // One action, then a recursive tail. Used for transactions that
  -- // contain 2+ top-level actions.
  -- ReplayActionsStep(before_tx, after_tx, before_chain, after_chain,
  --     private: mid_tx, mid_chain) = AND(
  --   ReplayAction(before_tx, mid_tx, before_chain, mid_chain)
  --   ReplayActions(mid_tx, after_tx, mid_chain, after_chain)
  -- )
  inductive ReplayActionsStep : (before_tx after_tx : Tx) → (before_chain after_chain : Chain) → Prop where
    | mk (before_tx after_tx : Tx) (before_chain after_chain : Chain)
      -- private
      (mid_tx : Tx)
      (mid_chain : Chain)
      -- statements
      (h1 : ReplayAction before_tx mid_tx before_chain mid_chain)
      (h2 : ReplayActions mid_tx after_tx mid_chain after_chain) :
      ReplayActionsStep before_tx after_tx before_chain after_chain

  -- // K=1 fast path: a single-event action whose only event is an Insert.
  -- // Same body as ReplayInsert, but the guard's chain bounds come from
  -- // the predicate's public args (`before_chain`/`after_chain`) instead
  -- // of `before_tx.chain_start`/`before_tx.chain_end`. Because the
  -- // action spans the whole chain range, the public args ARE the action's
  -- // chain scope, so the guard sees the same values it would have seen
  -- // inside a `ReplayAction`-materialized `inner_tx`. Skipping that
  -- // materialization is what saves the three intermediate statements.
  -- ReplayActionInsert(before_tx, after_tx, before_chain, after_chain,
  --     private: new, new_live, guard, initial) = AND(
  --   tx::TxInsert(after_chain, before_chain, initial, new, guard)
  --   SetInsert(before_tx.live, new, new_live)
  --   DictUpdate(before_tx, "live", new_live, after_tx)
  --   guard(new, before_chain, after_chain)
  -- )
  inductive ReplayActionInsert : (before_tx after_tx : Tx) → (before_chain after_chain : Chain) → Prop where
    | mk (before_tx after_tx : Tx) (before_chain after_chain : Chain)
      -- private
      (new : Object)
      (new_live : Finset Object)
      (guard : ObjectType)
      -- statements
      (h1 : TxInsert after_chain before_chain new guard)
      (h2 : SetInsert before_tx.live new new_live)
      (h3 : after_tx = {before_tx with live := new_live})
      (h4 : guard.Valid new before_chain after_chain) :
      ReplayActionInsert before_tx after_tx before_chain after_chain

  -- // ========================================================
  -- // Replay: Insert
  -- // ========================================================

  -- // Full insert replay: chain step (via TxInsert) + live update +
  -- // guard dispatch. Referencing TxInsert instead of re-proving the
  -- // Hash equations lets the prover reuse the record-time statement
  -- // that it already built for the application's action predicate.
  -- ReplayInsert(before_tx, after_tx, before_chain, after_chain,
  --     private: new, new_live, guard, initial) = AND(
  --   tx::TxInsert(after_chain, before_chain, initial, new, guard)
  --   SetInsert(before_tx.live, new, new_live)
  --   DictUpdate(before_tx, "live", new_live, after_tx)
  --   guard(new, before_tx.chain_start, before_tx.chain_end)
  -- )
  inductive ReplayInsert : (before_tx after_tx : Tx) → (before_chain after_chain : Chain) → Prop where
    | mk (before_tx after_tx : Tx) (before_chain after_chain : Chain)
      -- private
      (new : Object)
      (new_live : Finset Object)
      (guard : ObjectType)
      -- statements
      (h1 : TxInsert after_chain before_chain new guard)
      (h2 : SetInsert before_tx.live new new_live)
      (h3 : after_tx = {before_tx with live := new_live})
      (h4 : guard.Valid new before_tx.chain_start before_tx.chain_end) :
      ReplayInsert before_tx after_tx before_chain after_chain

  -- // ========================================================
  -- // Replay: Mutate
  -- // ========================================================

  -- // Nullifier computation and accumulation. Shared by mutate and
  -- // delete to prevent double-spending of the consumed object.
  -- // nullifier = H(H(obj, obj.key), "txlib-nullifier-v1")
  -- ReplayNullify(mid_tx, after_tx, old,
  --     private: obj_key_hash, nullifier, new_nullifiers) = AND(
  --   Hash(old, old.key, obj_key_hash)
  --   Hash(obj_key_hash, "txlib-nullifier-v1", nullifier)
  --   SetInsert(mid_tx.nullifiers, nullifier, new_nullifiers)
  --   DictUpdate(mid_tx, "nullifiers", new_nullifiers, after_tx)
  -- )
  inductive ReplayNullify : (mid_tx after_tx : Tx) → (old : Object) → Prop where
    | mk (mid_tx after_tx : Tx) (old : Object)
      -- private
      (nullifier : Nullifier)
      (new_nullifiers : Finset Nullifier)
      -- statements
      (h1 : nullifier = old.nullify)
      (h2 : SetInsert mid_tx.nullifiers nullifier new_nullifiers)
      (h3 : after_tx = { mid_tx with nullifiers := new_nullifiers }) :
      ReplayNullify mid_tx after_tx old

  -- // Live-set swap + nullifier accumulation. Chain/event-hash work is
  -- // delegated to TxMutate in the ReplayMutate parent.
  -- ReplayMutateEvent(before_tx, after_tx, old, new,
  --     private: new_live, live_mid, mid_tx) = AND(
  --   SetDelete(before_tx.live, old, live_mid)
  --   SetInsert(live_mid, new, new_live)
  --   DictUpdate(before_tx, "live", new_live, mid_tx)
  --   ReplayNullify(mid_tx, after_tx, old)
  -- )
  inductive ReplayMutateEvent : (before_tx after_tx : Tx) → (old new : Object) → Prop where
    | mk (before_tx after_tx : Tx) (old new : Object)
      -- private
      (new_live live_mid : Finset Object)
      (mid_tx : Tx)
      -- statements
      (h1 : SetDelete before_tx.live old live_mid)
      (h2 : SetInsert live_mid new new_live)
      (h3 : mid_tx = {before_tx with live := new_live})
      (h4: ReplayNullify mid_tx after_tx old) :
      ReplayMutateEvent before_tx after_tx old new


  -- // Full mutate replay: chain step (via TxMutate) + state update +
  -- // guard dispatch. The guard dispatches on `new` alone because
  -- // TxMutate's shared `type` arg already pins old.type == new.type.
  -- ReplayMutate(before_tx, after_tx, before_chain, after_chain,
  --     private: old, new, guard) = AND(
  --   tx::TxMutate(after_chain, before_chain, new, old, guard)
  --   ReplayMutateEvent(before_tx, after_tx, old, new)
  --   guard(new, before_tx.chain_start, before_tx.chain_end)
  -- )
  inductive ReplayMutate : (before_tx after_tx : Tx) → (before_chain after_chain : Chain) → Prop where
    | mk (before_tx after_tx : Tx) (before_chain after_chain : Chain)
      -- private
      (old new : Object)
      (guard : ObjectType)
      -- statements
      (h1 : TxMutate after_chain before_chain new old guard)
      (h2 : ReplayMutateEvent before_tx after_tx old new)
      (h3 : guard.Valid new before_tx.chain_start before_tx.chain_end) :
      ReplayMutate before_tx after_tx before_chain after_chain

  -- // ========================================================
  -- // Replay: Delete
  -- // ========================================================

  -- // Full delete replay: chain step (via TxDelete) + live-set removal
  -- // + nullifier accumulation + guard dispatch.
  -- ReplayDelete(before_tx, after_tx, before_chain, after_chain,
  --     private: old, guard, new_live, mid_tx) = AND(
  --   tx::TxDelete(after_chain, before_chain, old, guard)
  --   SetDelete(before_tx.live, old, new_live)
  --   DictUpdate(before_tx, "live", new_live, mid_tx)
  --   ReplayNullify(mid_tx, after_tx, old)
  --   guard(old, before_tx.chain_start, before_tx.chain_end)
  -- )
  inductive ReplayDelete : (before_tx after_tx : Tx) → (before_chain after_chain : Chain) → Prop where
    | mk (before_tx after_tx : Tx) (before_chain after_chain : Chain)
      -- private
      (old : Object)
      (guard : ObjectType)
      (new_live : Finset Object)
      (mid_tx : Tx)
      -- statements
      (h1 : TxDelete after_chain before_chain old guard)
      (h2 : SetDelete before_tx.live old new_live)
      (h3 : mid_tx = {before_tx with live := new_live})
      (h4 : ReplayNullify mid_tx after_tx old)
      (h5 : guard.Valid old before_tx.chain_start before_tx.chain_end) :
      ReplayDelete before_tx after_tx before_chain after_chain

  -- // ========================================================
  -- // Replay: List Structure
  -- // ========================================================
  -- //
  -- // The body of an action is a list of events (inserts, mutates,
  -- // deletes, sub-actions). ReplayContents is the predicate that walks
  -- // this list and applies each event's state change and guard dispatch
  -- // (see README.md for the conceptual pseudocode).
  -- //
  -- // Conceptually this is a for-loop, but in podlang it must be expressed
  -- // as a recursive OR: at each step the list is either a single trailing
  -- // event (the K=1 leaf, ReplayElement) or one head event followed by a
  -- // recursive ReplayContents call for the tail. Empty bodies are
  -- // forbidden by TxBuilder, so there's no K=0 leaf.
  -- //
  -- // A naive Step predicate would OR over all four event types inside
  -- // every recursion step. Instead, because the prover knows the head
  -- // event's type, it picks one of four specialised variants:
  -- //   StepInsert  -- head=Insert, tail=ReplayContents (K-1 elements)
  -- //   StepMutate  -- head=Mutate, tail=ReplayContents (K-1 elements)
  -- //   StepDelete  -- head=Delete, tail=ReplayContents (K-1 elements)
  -- //   StepAction  -- head=Action, tail=ReplayContents (K-1 elements)
  -- // Each variant fixes the head event's type at podlang level, folding
  -- // out the per-iteration OR-dispatch that ReplayElement still needs at
  -- // the trailing leaf.

  -- ReplayContents(before_tx, after_tx, before_chain, after_chain) = OR(
  --   ReplayElement(before_tx, after_tx, before_chain, after_chain)
  --   ReplayContentsStepInsert(before_tx, after_tx, before_chain, after_chain)
  --   ReplayContentsStepMutate(before_tx, after_tx, before_chain, after_chain)
  --   ReplayContentsStepDelete(before_tx, after_tx, before_chain, after_chain)
  --   ReplayContentsStepAction(before_tx, after_tx, before_chain, after_chain)
  -- )
  inductive ReplayContents : (before_tx after_tx : Tx) → (before_chain after_chain : Chain) → Prop where
    | element (before_tx after_tx : Tx) (before_chain after_chain : Chain)
      (h : ReplayElement before_tx after_tx before_chain after_chain) :
      ReplayContents before_tx after_tx before_chain after_chain
    | insert (before_tx after_tx : Tx) (before_chain after_chain : Chain)
      (h : ReplayContentsStepInsert before_tx after_tx before_chain after_chain) :
      ReplayContents before_tx after_tx before_chain after_chain
    | mutate (before_tx after_tx : Tx) (before_chain after_chain : Chain)
      (h : ReplayContentsStepMutate before_tx after_tx before_chain after_chain) :
      ReplayContents before_tx after_tx before_chain after_chain
    | delete (before_tx after_tx : Tx) (before_chain after_chain : Chain)
      (h : ReplayContentsStepDelete before_tx after_tx before_chain after_chain) :
      ReplayContents before_tx after_tx before_chain after_chain
    | action (before_tx after_tx : Tx) (before_chain after_chain : Chain)
      (h : ReplayContentsStepAction before_tx after_tx before_chain after_chain) :
      ReplayContents before_tx after_tx before_chain after_chain

  -- // The four specialised step variants. For Insert and Mutate the body
  -- // of `ReplayInsert`/`ReplayMutate` is inlined here -- both fit in 5
  -- // sub-statements alongside the recursive tail call. To stay within
  -- // pod2's 8-wildcard limit, head-event objects are packed into a small
  -- // private dict and accessed via anchored keys: `ins.new`/`ins.new_live`
  -- // for Insert, `pair.old`/`pair.new` for Mutate. Delete and Action
  -- // don't fit when inlined, so their step variants just call the
  -- // wrapping per-event predicate.
  -- ReplayContentsStepInsert(before_tx, after_tx, before_chain, after_chain,
  --     private: mid_tx, mid_chain, ins, guard) = AND(
  --   tx::TxInsert(mid_chain, before_chain, ins.initial, ins.new, guard)
  --   SetInsert(before_tx.live, ins.new, ins.new_live)
  --   DictUpdate(before_tx, "live", ins.new_live, mid_tx)
  --   guard(ins.new, before_tx.chain_start, before_tx.chain_end)
  --   ReplayContents(mid_tx, after_tx, mid_chain, after_chain)
  -- )
  inductive ReplayContentsStepInsert : (before_tx after_tx : Tx) → (before_chain after_chain : Chain) → Prop where
    | mk (before_tx after_tx : Tx) (before_chain after_chain : Chain)
      -- private
      (mid_tx : Tx)
      (mid_chain : Chain)
      (ins : Ins)
      (guard : ObjectType)
      -- statements
      (h1 : TxInsert mid_chain before_chain ins.new guard)
      (h2 : SetInsert before_tx.live ins.new ins.new_live)
      (h3 : mid_tx = {before_tx with live := ins.new_live})
      (h4 : guard.Valid ins.new before_tx.chain_start before_tx.chain_end)
      (h5 : ReplayContents mid_tx after_tx mid_chain after_chain) :
      ReplayContentsStepInsert before_tx after_tx before_chain after_chain

  -- ReplayContentsStepMutate(before_tx, after_tx, before_chain, after_chain,
  --     private: mid_tx, mid_chain, pair, guard) = AND(
  --   tx::TxMutate(mid_chain, before_chain, pair.new, pair.old, guard)
  --   ReplayMutateEvent(before_tx, mid_tx, pair.old, pair.new)
  --   guard(pair.new, before_tx.chain_start, before_tx.chain_end)
  --   ReplayContents(mid_tx, after_tx, mid_chain, after_chain)
  -- )
  inductive ReplayContentsStepMutate : (before_tx after_tx : Tx) → (before_chain after_chain : Chain) → Prop where
    | mk (before_tx after_tx : Tx) (before_chain after_chain : Chain)
      -- private
      (mid_tx : Tx)
      (mid_chain : Chain)
      (pair : Pair)
      (guard : ObjectType)
      -- statements
      (h1 : TxMutate mid_chain before_chain pair.new pair.old guard)
      (h2 : ReplayMutateEvent before_tx mid_tx pair.old pair.new)
      (h3 : guard.Valid pair.new before_tx.chain_start before_tx.chain_end)
      (h4 : ReplayContents mid_tx after_tx mid_chain after_chain) :
      ReplayContentsStepMutate before_tx after_tx before_chain after_chain

  -- ReplayContentsStepDelete(before_tx, after_tx, before_chain, after_chain,
  --     private: mid_tx, mid_chain) = AND(
  --   ReplayDelete(before_tx, mid_tx, before_chain, mid_chain)
  --   ReplayContents(mid_tx, after_tx, mid_chain, after_chain)
  -- )
  inductive ReplayContentsStepDelete : (before_tx after_tx : Tx) → (before_chain after_chain : Chain) → Prop where
    | mk (before_tx after_tx : Tx) (before_chain after_chain : Chain)
      -- private
      (mid_tx : Tx)
      (mid_chain : Chain)
      -- statements
      (h1 : ReplayDelete before_tx mid_tx before_chain mid_chain)
      (h2 : ReplayContents mid_tx after_tx mid_chain after_chain) :
      ReplayContentsStepDelete before_tx after_tx before_chain after_chain

  -- ReplayContentsStepAction(before_tx, after_tx, before_chain, after_chain,
  --     private: mid_tx, mid_chain) = AND(
  --   ReplayAction(before_tx, mid_tx, before_chain, mid_chain)
  --   ReplayContents(mid_tx, after_tx, mid_chain, after_chain)
  -- )
  inductive ReplayContentsStepAction : (before_tx after_tx : Tx) → (before_chain after_chain : Chain) → Prop where
    | mk (before_tx after_tx : Tx) (before_chain after_chain : Chain)
      -- private
      (mid_tx : Tx)
      (mid_chain : Chain)
      -- statements
      (h1 : ReplayAction before_tx mid_tx before_chain mid_chain)
      (h2 : ReplayContents mid_tx after_tx mid_chain after_chain) :
      ReplayContentsStepAction before_tx after_tx before_chain after_chain

  -- // A single element: one of the three event types, or a nested
  -- // action (which recursively contains its own ReplayContents).
  -- ReplayElement(before_tx, after_tx, before_chain, after_chain) = OR(
  --   ReplayInsert(before_tx, after_tx, before_chain, after_chain)
  --   ReplayMutate(before_tx, after_tx, before_chain, after_chain)
  --   ReplayDelete(before_tx, after_tx, before_chain, after_chain)
  --   ReplayAction(before_tx, after_tx, before_chain, after_chain)
  -- )
  inductive ReplayElement : (before_tx after_tx : Tx) → (before_chain after_chain : Chain) → Prop where
    | insert (before_tx after_tx : Tx) (before_chain after_chain : Chain)
      (h : ReplayInsert before_tx after_tx before_chain after_chain) :
      ReplayElement before_tx after_tx before_chain after_chain
    | mutate (before_tx after_tx : Tx) (before_chain after_chain : Chain)
      (h : ReplayMutate before_tx after_tx before_chain after_chain) :
      ReplayElement before_tx after_tx before_chain after_chain
    | delete (before_tx after_tx : Tx) (before_chain after_chain : Chain)
      (h : ReplayDelete before_tx after_tx before_chain after_chain) :
      ReplayElement before_tx after_tx before_chain after_chain
    | action (before_tx after_tx : Tx) (before_chain after_chain : Chain)
      (h : ReplayAction before_tx after_tx before_chain after_chain) :
      ReplayElement before_tx after_tx before_chain after_chain
end


mutual
  -- // ========================================================
  -- // Inputs Grounded
  -- // ========================================================
  -- //
  -- // InputsGrounded proves each input object is a member of `created`, the
  -- // global created-object set (every object state ever created, maintained
  -- // by the synchronizer).

  -- record StateHeader = (block_number, created, nullifiers, prior_state_history)

  -- InputsGrounded(inputs, created) = OR(
  --   // Base case: empty inputs. `created` is intentionally unconstrained --
  --   // an empty-input tx grounds nothing.
  --   Equal(inputs, {})
  --   InputsGroundedSingle(inputs, created)
  --   InputsGroundedPair(inputs, created)
  --   InputsGroundedRecursive(inputs, created)
  -- )
  inductive InputsGrounded : (inputs : Finset Object) → (created : List Object) → Prop where
    | empty (inputs : Finset Object) (created : List Object)
      (h : inputs = {}) :
      InputsGrounded inputs created
    | single (inputs : Finset Object) (created : List Object)
      (h : InputsGroundedSingle inputs created) :
      InputsGrounded inputs created
    | pair (inputs : Finset Object) (created : List Object)
      (h : InputsGroundedPair inputs created) :
      InputsGrounded inputs created
    | recursive (inputs : Finset Object) (created : List Object)
      (h : InputsGroundedRecursive inputs created) :
      InputsGrounded inputs created

  -- // Single-input fast path: avoids the cost of a recursive
  -- // InputsGrounded call.
  -- InputsGroundedSingle(inputs, created, private: input, index) = AND(
  --   ArrayContains(created, index, input)
  --   SetInsert({}, input, inputs)
  -- )
  inductive InputsGroundedSingle : (inputs : Finset Object) → (created : List Object) → Prop where
    | mk (inputs : Finset Object) (created : List Object)
      -- private
      (input : Object)
      (index : Nat)
      -- statements
      (h1 : ArrayContains created index input)
      (h2 : SetInsert {} input inputs) :
      InputsGroundedSingle inputs created

  -- // Two-input fast path: both inputs grounded inline, no sub-predicate
  -- // dispatch.
  -- InputsGroundedPair(inputs, created,
  --     private: first_input, second_input, set_first, first_index, second_index) = AND(
  --   ArrayContains(created, first_index, first_input)
  --   SetInsert({}, first_input, set_first)
  --   ArrayContains(created, second_index, second_input)
  --   SetInsert(set_first, second_input, inputs)
  -- )
  inductive InputsGroundedPair : (inputs : Finset Object) → (created : List Object) → Prop where
    | mk (inputs : Finset Object) (created : List Object)
      -- private
      (first_input second_input : Object)
      (set_first : Finset Object)
      (first_index second_index : Nat)
      -- statements
      (h1 : ArrayContains created first_index first_input)
      (h2 : SetInsert {} first_input set_first)
      (h3 : ArrayContains created second_index second_input)
      (h4 : SetInsert set_first second_input inputs) :
      InputsGroundedPair inputs created

  -- // 3+ inputs: ground two inputs, then recurse for the rest. The recursion
  -- // bottoms out at Single (odd N) or Pair (even N).
  -- InputsGroundedRecursive(inputs, created,
  --     private: first_input, second_input, mid, prev_inputs, first_index, second_index) = AND(
  --   ArrayContains(created, first_index, first_input)
  --   SetInsert(prev_inputs, first_input, mid)
  --   ArrayContains(created, second_index, second_input)
  --   SetInsert(mid, second_input, inputs)
  --   InputsGrounded(prev_inputs, created)
  -- )
  inductive InputsGroundedRecursive : (inputs : Finset Object) → (created : List Object) → Prop where
    | mk (inputs : Finset Object) (created : List Object)
      -- private
      (first_input second_input : Object)
      (mid prev_inputs : Finset Object)
      (first_index second_index : Nat)
      -- statements
      (h1 : ArrayContains created first_index first_input)
      (h2 : SetInsert prev_inputs first_input mid)
      (h3 : ArrayContains created second_index second_input)
      (h4 : SetInsert mid second_input inputs)
      (h5 : InputsGrounded prev_inputs created) :
      InputsGroundedRecursive inputs created
end

-- // ========================================================
-- // TxFinalized
-- // ========================================================
-- //
-- // The public entry point. A proof of TxFinalized is a self-contained
-- // certificate: it attests to the final state without revealing the
-- // event sequence that produced it.

-- // Exposes (state_header, tx_final, nullifiers, live) publicly. The
-- // verifier sees `state_header` as a single hash -- the commitment of the
-- // `StateHeader` record.
-- // tx_final is the after_tx dictionary commitment, which binds the
-- // live set, nullifiers, and final chain_start/chain_end together. Both
-- // the nullifier set and the final live set are also surfaced as their
-- // own public args (via TxFinalBindings) so the synchronizer can fold
-- // them into its global nullifier and created sets; the chain stays
-- // private. The top-level walker is ReplayActions, so every top-level
-- // event is guaranteed to be an action (no bare events can escape an
-- // action's guard dispatch).
-- //
-- // The DictInsert clause pins the full schema of `before_tx`:
-- // `nullifiers = {}` prevents a tx from inheriting nullifiers it did
-- // not emit itself, and `chain_start = chain_end = {}` removes the
-- // malleability that would otherwise let the prover witness arbitrary
-- // values for those two fields (they pass through ReplayActions
-- // verbatim into `tx_final`, since ReplayAction only updates the
-- // `live` and `nullifiers` keys).
-- TxFinalBindings(tx_final, nullifiers, live) = AND(
--   DictContains(tx_final, "nullifiers", nullifiers)
--   DictContains(tx_final, "live", live)
-- )
inductive TxFinalBindings : (tx_final : Tx) → (nullifiers : Finset Nullifier) → (live : Finset Object) → Prop where
  | mk (tx_final : Tx) (nullifiers : Finset Nullifier) (live : Finset Object)
    -- statements
    (h1 : nullifiers = tx_final.nullifiers)
    (h2 : live = tx_final.live) :
    TxFinalBindings tx_final nullifiers live

-- TxFinalized(state_header StateHeader, tx_final, nullifiers, live,
--      private: before_tx, chain_start, chain_final) = AND(
--   InputsGrounded(before_tx.live, state_header.created)
--   Hash(before_tx.live, {}, chain_start)
--   DictInsert({"nullifiers": {}, "chain_start": {}, "chain_end": {}}, "live", before_tx.live, before_tx)
--   TxFinalBindings(tx_final, nullifiers, live)
--   ReplayActions(before_tx, tx_final, chain_start, chain_final)
-- )
inductive TxFinalized : (state_header : StateHeader) → (tx_final : Tx) → (nullifiers : Finset Nullifier) → (live : Finset Object) → Prop where
  | mk (state_header : StateHeader) (tx_final : Tx) (nullifiers : Finset Nullifier) (live : Finset Object)
    -- private
    (before_tx : Tx)
    (chain_start chain_final : Chain)
    -- statements
    (h1 : InputsGrounded before_tx.live state_header.created)
    (h2 : chain_start = {init_live := before_tx.live, events := []})
    (h3 : before_tx = {live := before_tx.live, nullifiers := ∅, chain_start := {init_live := ∅, events := []}, chain_end := {init_live := ∅, events := []}})
    (h4 : TxFinalBindings tx_final nullifiers live)
    (h5 : ReplayActions before_tx tx_final chain_start chain_final) :
    TxFinalized state_header tx_final nullifiers live

end TxLib
