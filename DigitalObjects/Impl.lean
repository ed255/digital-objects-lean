import Mathlib.Data.Finset.Basic
import DigitalObjects.Spec
import DigitalObjects.TxLib

namespace Impl

-- Represents ~256 bit element (4 x Goldilocks prime field)
abbrev Hash := Nat

inductive Rel where
  | objsEq (i : Nat) (j : Nat)
  | objsNe (i : Nat) (j : Nat)
  deriving DecidableEq

mutual
  inductive Operation where
    | event (ev : Spec.SymbolicEvent)
    | subaction (a : Action) (mapping : List Nat)

  structure Action where
    relations : List Rel
    operations : List Operation
end

-- The automatic derivation of DecidableEq for recursive Operation/Action doesn't
-- go through, so we manually define it here.  This is a very mechanical
-- process.  DecidableEq carries the equality result and the proof.
mutual
  def Operation.decEq : (a b : Operation) → Decidable (a = b)
    | .event x, .event y => decidable_of_iff (x = y) (by simp)
    | .event _, .subaction _ _ => .isFalse nofun
    | .subaction _ _, .event _ => .isFalse nofun
    | .subaction a m, .subaction a' m' =>
      have := Action.decEq a a'
      decidable_of_iff (a = a' ∧ m = m') (by simp)
  termination_by a _ => sizeOf a

  def Operation.decEqList : (as bs : List Operation) → Decidable (as = bs)
    | [], [] => .isTrue rfl
    | [], _ :: _ => .isFalse nofun
    | _ :: _, [] => .isFalse nofun
    | a :: as, b :: bs =>
      have := Operation.decEq a b
      have := Operation.decEqList as bs
      decidable_of_iff (a = b ∧ as = bs) (by simp)
  termination_by as _ => sizeOf as

  def Action.decEq : (a b : Action) → Decidable (a = b)
    | ⟨r1, e1⟩, ⟨r2, e2⟩ =>
      have := Operation.decEqList e1 e2
      decidable_of_iff (r1 = r2 ∧ e1 = e2) (by simp)
  termination_by a _ => sizeOf a
end

instance : DecidableEq Operation := Operation.decEq
instance : DecidableEq Action := Action.decEq

structure ActionBridge where
  action : Action
  index : Nat
  deriving DecidableEq

structure ObjectType where
  bridges : List ActionBridge
  deriving DecidableEq

structure Object where
  type : ObjectType
  key : Nat
  data : List Nat
  deriving DecidableEq

def NullObject : Object := {
  type := { bridges := [] },
  key := 0,
  data := [],
}

-- There's a 1:1 mapping between nullifier and object state.  The real
-- implementation of the nullifier is `H(H(obj, obj.key), "txlib-nullifier-v1")`
-- which is injective modulo collision resistance, and we idealize it as the
-- identity for simplicity.  Currently we don't cover privacy in this model, so
-- we skip the property of "derivable only with knowledge of the key".
structure Nullifier where
  object : Object
  deriving DecidableEq

def Object.nullify (o : Object) : Nullifier :=
  ⟨o⟩

def Rel.toProp (r : Rel) (objects : Nat → Object) : Prop :=
  match r with
  | .objsEq i j => (objects i) = (objects j)
  | .objsNe i j => (objects i) ≠ (objects j)

mutual
  def Operation.toSpec (op : Operation) : (Spec.Operation Object) :=
    match op with
    | .event ev => .event ev
    -- An index beyond the mapping lists falls back to 0
    | .subaction a mapping => .subaction a.toSpec (fun i => mapping.getD i 0)
  termination_by sizeOf op

  def Action.toSpec (a : Action) : (Spec.Action Object) :=
    { relations := a.relations.map Rel.toProp
      operations := a.operations.map Operation.toSpec }
  termination_by sizeOf a
  decreasing_by
    rename_i h
    have := List.sizeOf_lt_of_mem h
    cases a; simp_all; omega
end

def ActionBridge.toSpec (b : ActionBridge) : (Spec.ActionBridge Object) :=
  {action := b.action.toSpec, index := b.index}

def ObjectType.toSpec (t : ObjectType) : (Spec.ObjectType Object) :=
  { bridges := t.bridges.map ActionBridge.toSpec }

-- TxLib models events as a hashed pair.  Because objects are non-empty
-- dictionaries (they need the "type" key), the three cases of hashed pair are
-- always distinguishable.  For simplicity we use a sum type
-- here.
abbrev Event := Spec.Event Object

-- The implementation commits to the initial live set when creating the chain,
-- but no further checks are performed.  Here we model this commitment as just
-- including the value in the Chain structure.
structure Chain where
  init_live : Finset Impl.Object
  events : List Event

-- The chain stores events newest first; `delta` is in chronological order
-- (oldest first), so it is reversed when prepended onto the chain.
def ChainDelta (chain_start chain_end : Chain) (delta : List Event) : Prop :=
  chain_end.events = delta.reverse ++ chain_start.events

def eventsObjects (events : List Event) : List Object :=
  events.flatMap (fun e =>
    match e with
    | .insert o => [o]
    | .mutate from_ to_ => [from_, to_]
    | .delete o => [o]
  )

mutual
  def ValidAction (a : Spec.Action Object) (evs : List Event) (objects : Nat → Object) : Prop :=
    (∀ r ∈ a.relations, r objects) ∧
    ValidActionOperations a.operations evs objects
  termination_by sizeOf a
  decreasing_by cases a; simp; omega

  def ValidActionOperations (ops : List (Spec.Operation Object)) (evs : List Event)
      (objects : Nat → Object) : Prop :=
    match ops, evs with
    | (.event ev) :: ops_tail, ev' :: evs_tail =>
      (ev.map objects) = ev' ∧ ValidActionOperations ops_tail evs_tail objects
    | (.subaction a mapping) :: ops_tail, evs =>
      ∃ evs_sub evs_rest, evs_sub ++ evs_rest = evs ∧
        ValidAction a evs_sub (Spec.reindex objects mapping) ∧
        ValidActionOperations ops_tail evs_rest objects
    | [], [] => True
    | _, _ => False
  termination_by sizeOf ops

end

-- Prop: validate a type guard against an object for a particular chain of
-- events.  This predicate intentionally doesn't verify that `o.type = t`
-- because this is a model of the following podlang statement template:
-- `guard(new, chain_start, chain_end)`
def ObjectType.Valid (t : ObjectType) (o : Object) (chain_start chain_end : Chain) : Prop :=
  ∃ events, ChainDelta chain_start chain_end events ∧
  let objects := (fun i => (eventsObjects events).getD i NullObject)
  ∃ b ∈ t.toSpec.bridges,
    ValidAction b.action events objects ∧
    (b.action.localObjects objects)[b.index]? = some o

--
-- Synchronizer procedure
--

structure TxPayload where
  -- The Tx to be applied
  tx_final : TxLib.Tx
  -- The grounding state
  state_header : TxLib.StateHeader
  -- The grounding state index
  state_header_index : Nat
  -- The set of nullifiers for this tx (corresponds to consumed objects)
  nullifiers : List Nullifier
  -- The set of new live objects after this tx (corresponds to created objects)
  live : List Object
  -- Proof of TxFinalized
  proof : TxLib.TxFinalized state_header tx_final nullifiers.toFinset live.toFinset

def genesisState : TxLib.StateHeader :=
  { block_number := 0
    created := []
    nullifiers := ∅
    prior_state_history := [] }

def applyTx (state : TxLib.StateHeader) (tx : TxPayload) : Option TxLib.StateHeader :=
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
