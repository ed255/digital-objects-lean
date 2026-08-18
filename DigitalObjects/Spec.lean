import Mathlib.Data.Set.Basic

namespace Spec

-- Type: Observable effect on the system state
inductive Effect (Object : Type) where
  | create (o : Object)
  | consume (o : Object)

-- Prop: The effect list is valid given the sets of already created/consumed
-- objects: each create is fresh, each consume was created and not yet consumed
def ValidEffects {Object : Type} (created consumed : Set Object) :
    List (Effect Object) → Prop
  | [] => True
  | .create o :: es => o ∉ created ∧ ValidEffects (insert o created) consumed es
  | .consume o :: es => o ∈ created ∧ o ∉ consumed ∧ ValidEffects created (insert o consumed) es

-- Type: event affecting objects (symbolic or concrete)
inductive Event (α : Type) where
  | insert (x : α)
  | delete (x : α)
  | mutate (from_ to_ : α)
  deriving DecidableEq

abbrev SymbolicEvent := Event Nat
abbrev ConcreteEvent {Object : Type} := Event Object

-- Fun: Map a symbolic event to an event with concrete objects
def SymbolicEvent.map {Object : Type} (objects : Nat → Object) : SymbolicEvent → (@ConcreteEvent Object)
  | .insert i => .insert (objects i)
  | .delete i => .delete (objects i)
  | .mutate i j => .mutate (objects i) (objects j)

-- Fun: Return the effects of a concrete event
def ConcreteEvent.toEffects {Object : Type} : @ConcreteEvent Object → List (Effect Object)
  | .insert o => [.create o]
  | .delete o => [.consume o]
  | .mutate o₁ o₂ => [.consume o₁, .create o₂]

-- Prop: A concrete event creates or consumes an object
def ConcreteEvent.Touches {Object : Type} : @ConcreteEvent Object → Object → Prop
  | .insert o', o => o' = o
  | .delete o', o => o' = o
  | .mutate o₁ o₂, o => o₁ = o ∨ o₂ = o

mutual
  -- Type: A state affecting operation within an action
  inductive Operation (Object : Type) where
    | event (ev : SymbolicEvent)
    | subaction (a : Action Object) (mapping : Nat → Nat)

  -- Type: A collection of object relations and state changes
  structure Action (Object : Type) where
    relations : List ((Nat → Object) → Prop)
    operations : List (Operation Object)
end

-- Type: The attempt at applying an action with concrete objects
structure Tx (Object : Type) where
  action : Action Object
  objects : Nat → Object

-- Type: Bridge an action with a particular object it directly touches
-- identified by index
structure ActionBridge (Object : Type) where
  action : Action Object
  index : Nat

-- Type: The set of valid actions of an object
structure ObjectType (Object : Type) where
  bridges : List (ActionBridge Object)

-- Prop: Mutation preserves object type
def ConcreteEvent.TypePreserving {Object : Type}
  (typeOf : Object → (ObjectType Object)): (@ConcreteEvent Object) → Prop
  | .mutate o₁ o₂ => (typeOf o₁) = (typeOf o₂)
  | _ => True

-- Fun: Reindex parent's objects through a subaction's mapping.
def reindex {Object : Type}
    (objects : Nat → Object)
    (mapping : Nat → Nat) :
    Nat → Object :=
  fun i => objects (mapping i)

-- Fun: List of objects that an action directly touches, ignoring subactions
def Action.localObjects {Object : Type}
  (a : Action Object) (objects : Nat → Object) : List Object :=
  a.operations.flatMap (fun e =>
    match e with
    | .event ev => (match (ev.map objects) with
      | .insert o => [o]
      | .mutate from_ to_ => [from_, to_]
      | .delete o => [o])
    | .subaction _ _ => [])

-- Prop: All objects touched by this action (ignoring subactions) are touched
-- by an action in the object's type with a valid bridge index
def Action.OpsTypeMatch {Object : Type}
  (typeOf : Object → ObjectType Object)
  (a : Action Object) (objects : Nat → Object) : Prop :=
  ∀ (i : Nat) (o : Object), (a.localObjects objects)[i]? = some o →
    ∃ b ∈ (typeOf o).bridges, a = b.action ∧ i = b.index

-- NOTE: These mutually recursive function definitions work on mutual recursive
-- types.  Lean requires a proof of termination so that we can use this
-- function in propositions.
mutual
  -- Fun: List of concrete events of this operation and nested actions
  def Operation.concreteEvents {Object : Type}
    (e : Operation Object) (objects : Nat → Object) : List (@ConcreteEvent Object) :=
    match e with
    | .event ev => [ev.map objects]
    | .subaction a mapping => a.concreteEvents (reindex objects mapping)
  termination_by sizeOf e

  -- Fun: List of concrete events of this action's operations and nested actions
  def Action.concreteEvents {Object : Type}
    (a : Action Object) (objects : Nat → Object) : List (@ConcreteEvent Object) :=
    (a.operations.attach.map fun ⟨e, _⟩ => e.concreteEvents objects).flatten
  termination_by sizeOf a
  decreasing_by
    rename_i h
    have := List.sizeOf_lt_of_mem h;
    cases a; simp_all; omega
end

-- Fun: List of effects of an action
def Action.effects {Object : Type}
  (a : Action Object) (objects : Nat → Object) : List (Effect Object) :=
  (a.concreteEvents objects).flatMap (fun ev => ev.toEffects)


mutual
  -- Prop: True if P holds at every action and subaction reachable from this operation
  inductive Operation.AllSubactions {Object : Type}
      (P : Action Object → (Nat → Object) → Prop) :
      Operation Object → (Nat → Object) → Prop where
    | event {objects : Nat → Object} {ev : SymbolicEvent} :
        Operation.AllSubactions P (Operation.event ev) objects
    | subaction {objects : Nat → Object}
        (a : Action Object) (mapping : Nat → Nat)
        (h_rec : Action.AllSubactions P a (reindex objects mapping)) :
        Operation.AllSubactions P (Operation.subaction a mapping) objects

  -- Prop: True if P holds at this action and every subaction reachable from it
  inductive Action.AllSubactions {Object : Type}
      (P : Action Object → (Nat → Object) → Prop) :
      Action Object → (Nat → Object) → Prop where
    | mk {a : Action Object} {objects : Nat → Object}
        (h_here : P a objects)
        (h_operations : ∀ e ∈ a.operations, Operation.AllSubactions P e objects) :
        Action.AllSubactions P a objects
end

-- Prop: All relations in nested actions of the tx hold
def Tx.RelationsHold {Object : Type} (tx : Tx Object) : Prop :=
  Action.AllSubactions
    (fun a objects => ∀ rel ∈ a.relations, rel objects)
    tx.action tx.objects

-- Prop: The object has been created in the history
def InCreated {Object : Type} (o : Object) (h : List (Tx Object)) : Prop :=
  ∃ tx ∈ h, Effect.create o ∈ tx.action.effects tx.objects

-- Prop: The object has been consumed in the history
def InConsumed {Object : Type} (o : Object) (h : List (Tx Object)) : Prop :=
  ∃ tx ∈ h, Effect.consume o ∈ tx.action.effects tx.objects

-- The history is defined as a list of transactions, where the head is the most
-- recent transaction.
structure SystemSpec (Object : Type) (TxPayload : Type) [DecidableEq Object] where
  -- Properties that an implementation must define --
  -- Prop: A transaction is valid to append to a history
  ValidTx : List TxPayload → TxPayload → Prop
  -- Fun: returns the type of the object
  typeOf (o : Object) : ObjectType Object
  -- Fun: semantic transaction content of an implementation dependent transaction payload
  specTx : TxPayload -> Tx Object

  -- Theorems that an implementation must prove --

  -- Obligation: The effects in a tx are valid:
  -- create:
  -- * the object was not previously created (in a previous tx, or in a previous effect in the tx)
  -- consume:
  -- * the object was previously created (in a previous tx, or in a previous effect in the tx)
  -- * the object was not previously consumed (in a previous tx, or in a previous effect in the tx)
  validTx_effects :
    ∀ h tx, ValidTx h tx →
    let h' := h.map specTx
    let tx' := specTx tx
    ValidEffects {o | InCreated o h'} {o | InConsumed o h'} (tx'.action.effects tx'.objects)

  -- Obligation: A mutate event is valid if it preserves the type of the object
  validTx_mutate :
    ∀ h tx, ValidTx h tx →
    let tx' := specTx tx
    ∀ ev ∈ (tx'.action.concreteEvents tx'.objects), ev.TypePreserving typeOf
    -- NOTE: In a future iteration we may say that the identity is preserved

  -- Obligation: A transaction is valid if all the reations in actions and subactions hold
  validTx_relations_hold :
    ∀ h tx, ValidTx h tx →
    let tx' := specTx tx
    Tx.RelationsHold tx'

  -- Obligation: A transaction is valid if all touched objects are touched via events
  -- in actions that belong to their type
  validTx_ops_type_match:
    ∀ h tx, ValidTx h tx →
    let tx' := specTx tx
    Action.AllSubactions (Action.OpsTypeMatch typeOf) tx'.action tx'.objects

-- Definitions

namespace SystemSpec

-- Prop: The history is valid.  An sound implementation must prove this proposition.
def ValidHistory {Object : Type} {TxPayload : Type} [DecidableEq Object] (spec : SystemSpec Object TxPayload) :
    List TxPayload → Prop
  | [] => True
  | tx :: history => spec.ValidHistory history ∧ spec.ValidTx history tx

end SystemSpec

-- Prop: History h happened before h'
def Reaches  {Object : Type} (h h' : List (Tx Object)) : Prop :=  h.IsSuffix h'

-- Generic theorems with proofs (for all SystemSpec)

-- Theorem: If created before, created after
theorem InCreated.mono {Object : Type} {o : Object} {h h' : List (Tx Object)} :
    Reaches h h' → InCreated o h → InCreated o h' := by
  intro hreach ⟨tx, htx_mem, htx_creates⟩
  exact ⟨tx, hreach.mem htx_mem, htx_creates⟩

-- Theorem: If consumed before, consumed after
theorem InConsumed.mono {Object : Type} {o : Object} {h h' : List (Tx Object)} :
    Reaches h h' → InConsumed o h → InConsumed o h' := by
  intro hreach ⟨tx, htx_mem, htx_consumes⟩
  exact ⟨tx, hreach.mem htx_mem, htx_consumes⟩

-- Thereom: The genesis has no created or consumed objects
theorem genesis_empty {Object : Type} {o : Object} :
    (¬ InCreated o []) ∧ (¬ InConsumed o []) := by
    simp [InCreated, InConsumed]

-- TODO: Write theorems that say: things like
-- * There's no way to delete an object except by running an action that consumes it defined by its type
-- * There's no way to create an object except by running an action that creates it defined by its type
-- * There's no way to mutate an object except by running an action that mutates it defined by its type

end Spec
