-- Simplified versions of TxLib predicates.  Equivalence proven in
-- `PredicatesSimpleProofs.lean`

import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Relation
import DigitalObjects.Impl.Defs
import DigitalObjects.Impl.TxLib.Events
import DigitalObjects.Impl.TxLib.Predicates

namespace TxLib
open Impl (Object Nullifier Chain StateHeader)

--
-- Stage 0: Simplified individual predicates.
--

def InputsGroundedSimple0 (inputs : Finset Object) (created : List Object) : Prop :=
  ∀ input ∈ inputs, input ∈ created

-- Prop: one-or-more ReplayAction steps chained through intermediate (tx, chain) states.
def ReplayActionsSimple0 (before_tx after_tx : Tx) (before_chain after_chain : Chain) : Prop :=
  Relation.TransGen (fun before after : Tx × Chain => ReplayAction before.1 after.1 before.2 after.2)
    (before_tx, before_chain) (after_tx, after_chain)

-- Prop: one-or-more ReplayElement steps chained through intermediate (tx, chain) states.
def ReplayContentsSimple0 (before_tx after_tx : Tx) (before_chain after_chain : Chain) : Prop :=
  Relation.TransGen (fun before after : Tx × Chain => ReplayElement before.1 after.1 before.2 after.2)
    (before_tx, before_chain) (after_tx, after_chain)

--
-- Stage 1: Simplified mutually-dependent predicates.
--

mutual
  inductive ReplayActionSimple : (before_tx after_tx : Tx) → (before_chain after_chain : Chain) → Prop where
    | mk (before_tx after_tx : Tx) (before_chain after_chain : Chain)
      -- private
      (scope_mid inner_tx end_tx mid : Tx)
      -- statements
      (h1 : scope_mid = {before_tx with chain_start := before_chain})
      (h2 : inner_tx = {scope_mid with chain_end := after_chain})
      (h3 : ReplayContentsSimple inner_tx end_tx before_chain after_chain)
      (h4 : mid = {before_tx with live := end_tx.live})
      (h5 : after_tx = {mid with nullifiers := end_tx.nullifiers}) :
      ReplayActionSimple before_tx after_tx before_chain after_chain

  inductive ReplayElementSimple : (before_tx after_tx : Tx) → (before_chain after_chain : Chain) → Prop where
    | insert (before_tx after_tx : Tx) (before_chain after_chain : Chain)
      (h : ReplayInsert before_tx after_tx before_chain after_chain) :
      ReplayElementSimple before_tx after_tx before_chain after_chain
    | mutate (before_tx after_tx : Tx) (before_chain after_chain : Chain)
      (h : ReplayMutate before_tx after_tx before_chain after_chain) :
      ReplayElementSimple before_tx after_tx before_chain after_chain
    | delete (before_tx after_tx : Tx) (before_chain after_chain : Chain)
      (h : ReplayDelete before_tx after_tx before_chain after_chain) :
      ReplayElementSimple before_tx after_tx before_chain after_chain
    | action (before_tx after_tx : Tx) (before_chain after_chain : Chain)
      (h : ReplayActionSimple before_tx after_tx before_chain after_chain) :
      ReplayElementSimple before_tx after_tx before_chain after_chain

  -- Prop: one-or-more ReplayElementSimple steps chained through intermediate
  -- (tx, chain) states.  This is `Relation.TransGen` spelled out as an
  -- inductive (constructors mirror TransGen.single/TransGen.head): a `def`
  -- using TransGen cannot appear in this mutual block, and the kernel rejects
  -- nesting ReplayElementSimple inside TransGen's relation parameter.
  inductive ReplayContentsSimple : (before_tx after_tx : Tx) → (before_chain after_chain : Chain) → Prop where
    | single (before_tx after_tx : Tx) (before_chain after_chain : Chain)
      (h : ReplayElementSimple before_tx after_tx before_chain after_chain) :
      ReplayContentsSimple before_tx after_tx before_chain after_chain
    | head (before_tx mid_tx after_tx : Tx) (before_chain mid_chain after_chain : Chain)
      (h1 : ReplayElementSimple before_tx mid_tx before_chain mid_chain)
      (h2 : ReplayContentsSimple mid_tx after_tx mid_chain after_chain) :
      ReplayContentsSimple before_tx after_tx before_chain after_chain
end

def ReplayActionsSimple (before_tx after_tx : Tx) (before_chain after_chain : Chain) : Prop :=
  Relation.TransGen (fun before after : Tx × Chain => ReplayActionSimple before.1 after.1 before.2 after.2)
    (before_tx, before_chain) (after_tx, after_chain)

inductive TxFinalizedSimple : (state_header : StateHeader) → (tx_final : Tx) → (nullifiers : Finset Nullifier) → (live : Finset Object) → Prop where
  | mk (state_header : StateHeader) (tx_final : Tx) (nullifiers : Finset Nullifier) (live : Finset Object)
    -- private
    (before_tx : Tx)
    (chain_start chain_final : Chain)
    -- statements
    (h1 : InputsGroundedSimple0 before_tx.live state_header.created)
    (h2 : chain_start = {init_live := before_tx.live, events := []})
    (h3 : before_tx = {live := before_tx.live, nullifiers := ∅, chain_start := {init_live := ∅, events := []}, chain_end := {init_live := ∅, events := []}})
    (h4 : nullifiers = tx_final.nullifiers)
    (h5 : live = tx_final.live)
    (h6 : ReplayActionsSimple before_tx tx_final chain_start chain_final) :
    TxFinalizedSimple state_header tx_final nullifiers live

end TxLib
