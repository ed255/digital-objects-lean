-- Simplified predicates with equivalence proofs.
-- The content of this file is mostly LLM generated, including comments

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import DigitalObjects.Impl.TxLib.Predicates
import DigitalObjects.Impl.TxLib.PredicatesSimple
import DigitalObjects.Impl.Defs

namespace TxLib
open Impl (Object Nullifier Chain StateHeader)

--
-- Stage 0
--

--
-- # InputsGrounded ↔ InputsGroundedSimple0
--
-- How it's structured
--
-- Faithful → simple (toSimple0 family): structural recursion on the derivation.
-- Single/Pair aren't recursive, so they're standalone theorems before the
-- mutual block — only InputsGrounded ↔ InputsGroundedRecursive need mutual
-- recursion (mirroring which podlang predicates actually recurse). The obtain
-- ⟨-, rfl⟩ patterns see straight through your SetInsert def to its ∉ ∧ insert
-- body, substituting the set equations; then simp turns x ∈ insert … (insert …
-- ∅) into the disjunction of cases.
--
-- Simple0 → faithful (ofSimple0): well-founded recursion on inputs.card with the
-- three-way split card = 0 / = 1 / > 1:
-- - 0 → empty; 1 → single (Finset.card_eq_one gives inputs = {x}).
-- - > 1 → Finset.one_lt_card yields distinct a ≠ b, both members; prev :=
--   (inputs.erase b).erase a; the two Finset.insert_erase rewrites reassemble
--   inputs = insert b (insert a prev). Note how your strict SetInsert pays off
--   here: the ∉ obligations are exactly Finset.notMem_erase — the erase
--   decomposition produces precisely the disjointness facts the constructor
--   demands.
-- - termination_by inputs.card + decreasing_by: two card_erase_of_mem facts
--   and omega — same recipe as your other termination proofs.
--
-- Worth noting: pair is confirmed dead weight in this direction: ofSimple0
-- never constructs it — even-cardinality inputs bottom out through recursive →
-- … → empty. So the equivalence also documents that Pair is a pure
-- prover-optimization (it's still needed in toSimple0, i.e. its existence
-- doesn't break soundness — which is the actual claim worth having on record).

-- helper: indexed lookup implies membership
private theorem mem_of_getElem? {α : Type} {l : List α} {i : Nat} {a : α}
    (h : l[i]? = some a) : a ∈ l := by
  rw [List.getElem?_eq_some_iff] at h
  obtain ⟨hlt, rfl⟩ := h
  exact List.getElem_mem hlt

-- helper: membership implies an indexed lookup
private theorem mem_getElem? {α : Type} {l : List α} {a : α}
    (h : a ∈ l) : ∃ i : Nat, l[i]? = some a := by
  obtain ⟨i, hlt, rfl⟩ := List.mem_iff_getElem.mp h
  exact ⟨i, by simp [hlt]⟩

theorem InputsGroundedSingle.toSimple0 {inputs : Finset Object} {created : List Object}
    (h : InputsGroundedSingle inputs created) : InputsGroundedSimple0 inputs created := by
  obtain ⟨_, _, input, index, h1, ⟨-, rfl⟩⟩ := h
  intro x hx
  simp at hx
  subst hx
  exact mem_of_getElem? h1

theorem InputsGroundedPair.toSimple0 {inputs : Finset Object} {created : List Object}
    (h : InputsGroundedPair inputs created) : InputsGroundedSimple0 inputs created := by
  obtain ⟨_, _, first, second, set_first, i, j, h1, ⟨-, rfl⟩, h3, ⟨-, rfl⟩⟩ := h
  intro x hx
  simp at hx
  rcases hx with rfl | rfl
  · exact mem_of_getElem? h3
  · exact mem_of_getElem? h1

mutual
  theorem InputsGrounded.toSimple0 {inputs : Finset Object} {created : List Object}
      (h : InputsGrounded inputs created) : InputsGroundedSimple0 inputs created :=
    match h with
    | .empty _ _ h => by subst h; intro x hx; simp at hx
    | .single _ _ h => h.toSimple0
    | .pair _ _ h => h.toSimple0
    | .recursive _ _ h => h.toSimple0

  theorem InputsGroundedRecursive.toSimple0 {inputs : Finset Object} {created : List Object}
      (h : InputsGroundedRecursive inputs created) : InputsGroundedSimple0 inputs created :=
    match h with
    | .mk _ _ first second mid prev i j h1 h2 h3 h4 h5 => by
      obtain ⟨-, rfl⟩ := h2
      obtain ⟨-, rfl⟩ := h4
      have ih := h5.toSimple0
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | hx
      · exact mem_of_getElem? h3
      · exact mem_of_getElem? h1
      · exact ih x hx
end

theorem InputsGrounded.ofSimple0 (inputs : Finset Object) (created : List Object)
    (h : InputsGroundedSimple0 inputs created) : InputsGrounded inputs created := by
  obtain hc | hc | hc : inputs.card = 0 ∨ inputs.card = 1 ∨ 1 < inputs.card := by omega
  · exact .empty _ _ (Finset.card_eq_zero.mp hc)
  · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hc
    obtain ⟨i, hi⟩ := mem_getElem? (h x (Finset.mem_singleton_self x))
    exact .single _ _ (.mk _ _ x i hi ⟨Finset.notMem_empty x, by simp⟩)
  · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hc
    have hab' : a ∈ inputs.erase b := Finset.mem_erase.mpr ⟨hab, ha⟩
    obtain ⟨i, hi⟩ := mem_getElem? (h a ha)
    obtain ⟨j, hj⟩ := mem_getElem? (h b hb)
    have hrec : InputsGrounded ((inputs.erase b).erase a) created :=
      InputsGrounded.ofSimple0 _ created fun x hx =>
        h x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))
    refine .recursive _ _ (.mk _ _ a b _ _ i j hi ⟨Finset.notMem_erase a _, rfl⟩ hj
      ⟨?_, ?_⟩ hrec)
    · rw [Finset.insert_erase hab']
      exact Finset.notMem_erase b inputs
    · rw [Finset.insert_erase hab', Finset.insert_erase hb]
termination_by inputs.card
decreasing_by
  have h1 : (inputs.erase b).card = inputs.card - 1 := Finset.card_erase_of_mem hb
  have h2 : ((inputs.erase b).erase a).card = (inputs.erase b).card - 1 :=
    Finset.card_erase_of_mem hab'
  omega

theorem inputsGrounded_iff_inputsGroundedSimple0 (inputs : Finset Object) (created : List Object) :
    InputsGrounded inputs created ↔ InputsGroundedSimple0 inputs created :=
  ⟨InputsGrounded.toSimple0, InputsGrounded.ofSimple0 inputs created⟩

--
-- # ReplayActions ↔ ReplayActionsSimple0
--
-- How it works
--
-- ReplayActionInsert.toReplayAction — the heart of the proof. It builds the
-- 5-statement long derivation from the 2-statement fast path, supplying
-- ReplayAction's four private Txs explicitly (scope_mid, inner_tx, end_tx, mid
-- as concrete {before_tx with …} updates). Everything then discharges by rfl
-- or by reusing the fast path's own hypotheses unchanged — most notably h4 :
-- guard.Valid new before_chain after_chain is accepted where ReplayInsert
-- demands guard.Valid new inner_tx.chain_start inner_tx.chain_end, because
-- after the two structure updates those projections reduce definitionally to
-- before_chain/after_chain. That defeq is precisely the podlang comment's
-- claim ("the public args ARE the action's chain scope") — the model validates
-- it, no rewriting needed. Same for the final h3: the long path's after_tx =
-- {mid with nullifiers := end_tx.nullifiers} reduces to the fast path's
-- after_tx = {before_tx with live := new_live}.
--
-- - toSimple0 — the mutual pair mirrors which predicates are actually mutually
--   recursive (ReplayActions ↔ ReplayActionsStep), same pattern as the
--   InputsGrounded proofs: action → TransGen.single, actions_step →
--   TransGen.head, and action_insert → TransGen.single via the fast-path lemma.
--
-- - ofSimple0 — stated over pairs p q : Tx × Chain so the TransGen motive is
--   directly usable, then head_induction_on peels one ReplayAction at a time
--   into action/actions_step constructors. The final iff applies it at literal
--   pairs, where p.1/p.2 reduce, so no repackaging lemma is needed.

-- Soundness of the K=1 fast path: everything ReplayActionInsert proves, the
-- long path (ReplayAction → ReplayContents → ReplayElement → ReplayInsert)
-- proves as well.  This discharges the claim made in the podlang comment:
-- the guard sees the same chain bounds either way.
theorem ReplayActionInsert.toReplayAction
    {before_tx after_tx : Tx} {before_chain after_chain : Chain}
    (h : ReplayActionInsert before_tx after_tx before_chain after_chain) :
    ReplayAction before_tx after_tx before_chain after_chain := by
  obtain ⟨_, _, _, _, new, new_live, guard, h1, h2, h3, h4⟩ := h
  exact .mk _ _ _ _
    {before_tx with chain_start := before_chain}
    {before_tx with chain_start := before_chain, chain_end := after_chain}
    {before_tx with chain_start := before_chain, chain_end := after_chain, live := new_live}
    {before_tx with live := new_live}
    rfl rfl
    (.element _ _ _ _ (.insert _ _ _ _ (.mk _ _ _ _ new new_live guard h1 h2 rfl h4)))
    rfl h3

mutual
  theorem ReplayActions.toSimple0 {before_tx after_tx : Tx} {before_chain after_chain : Chain}
      (h : ReplayActions before_tx after_tx before_chain after_chain) :
      ReplayActionsSimple0 before_tx after_tx before_chain after_chain :=
    match h with
    | .action _ _ _ _ h => Relation.TransGen.single h
    | .actions_step _ _ _ _ h => h.toSimple0
    | .action_insert _ _ _ _ h => Relation.TransGen.single h.toReplayAction

  theorem ReplayActionsStep.toSimple0 {before_tx after_tx : Tx} {before_chain after_chain : Chain}
      (h : ReplayActionsStep before_tx after_tx before_chain after_chain) :
      ReplayActionsSimple0 before_tx after_tx before_chain after_chain :=
    match h with
    | .mk _ _ _ _ _ _ h1 h2 => Relation.TransGen.head h1 h2.toSimple0
end

theorem ReplayActions.ofSimple0 {p q : Tx × Chain}
    (h : Relation.TransGen (fun before after : Tx × Chain => ReplayAction before.1 after.1 before.2 after.2) p q) :
    ReplayActions p.1 q.1 p.2 q.2 := by
  induction h using Relation.TransGen.head_induction_on with
  | single h => exact .action _ _ _ _ h
  | head h1 _ ih => exact .actions_step _ _ _ _ (.mk _ _ _ _ _ _ h1 ih)

theorem replayActions_iff_replayActionsSimple0 (before_tx after_tx : Tx) (before_chain after_chain : Chain) :
    ReplayActions before_tx after_tx before_chain after_chain ↔
      ReplayActionsSimple0 before_tx after_tx before_chain after_chain :=
  ⟨ReplayActions.toSimple0, ReplayActions.ofSimple0⟩

--
-- # ReplayContents ↔ ReplayContentsSimple0
--
-- Same architecture as the ReplayActions proof, scaled to five mutual
-- branches:
--
-- - toSimple0 — one theorem per predicate in the mutual cluster. The
--   interesting arms are StepInsert/StepMutate: their constructor fields are
--   repacked verbatim into a ReplayInsert.mk/ReplayMutate.mk (note h1 h2 h3 h4
--   pass through unchanged — the inlined clauses are definitionally the
--   standalone predicate's clauses, with ins.new/pair.old projections reducing
--   where needed). This is the checked version of your podlang comment "the body
--   of ReplayInsert/ReplayMutate is inlined here": if the inlining ever drifts
--   from the standalone predicate, these two arms stop compiling.
--   StepDelete/StepAction just wrap their h1 in the corresponding ReplayElement
--   constructor, since they delegate rather than inline.
--
-- - ofSimple0 — head_induction_on again; each peeled ReplayElement head is
--   case-split and rebuilt as the matching Step* constructor, packing the loose
--   fields back into the Ins/Pair records (⟨new, new_live⟩, ⟨old, new⟩) with the
--   tail supplied by the induction hypothesis.

-- The four Step* variants are sound inlinings: each proves exactly one
-- ReplayElement head followed by a ReplayContents tail.
mutual
  theorem ReplayContents.toSimple0 {before_tx after_tx : Tx} {before_chain after_chain : Chain}
      (h : ReplayContents before_tx after_tx before_chain after_chain) :
      ReplayContentsSimple0 before_tx after_tx before_chain after_chain :=
    match h with
    | .element _ _ _ _ h => Relation.TransGen.single h
    | .insert _ _ _ _ h => h.toSimple0
    | .mutate _ _ _ _ h => h.toSimple0
    | .delete _ _ _ _ h => h.toSimple0
    | .action _ _ _ _ h => h.toSimple0

  theorem ReplayContentsStepInsert.toSimple0 {before_tx after_tx : Tx} {before_chain after_chain : Chain}
      (h : ReplayContentsStepInsert before_tx after_tx before_chain after_chain) :
      ReplayContentsSimple0 before_tx after_tx before_chain after_chain :=
    match h with
    | .mk _ _ _ _ _ _ ins guard h1 h2 h3 h4 h5 =>
      Relation.TransGen.head
        (.insert _ _ _ _ (.mk _ _ _ _ ins.new ins.new_live guard h1 h2 h3 h4)) h5.toSimple0

  theorem ReplayContentsStepMutate.toSimple0 {before_tx after_tx : Tx} {before_chain after_chain : Chain}
      (h : ReplayContentsStepMutate before_tx after_tx before_chain after_chain) :
      ReplayContentsSimple0 before_tx after_tx before_chain after_chain :=
    match h with
    | .mk _ _ _ _ _ _ pair guard h1 h2 h3 h4 =>
      Relation.TransGen.head
        (.mutate _ _ _ _ (.mk _ _ _ _ pair.old pair.new guard h1 h2 h3)) h4.toSimple0

  theorem ReplayContentsStepDelete.toSimple0 {before_tx after_tx : Tx} {before_chain after_chain : Chain}
      (h : ReplayContentsStepDelete before_tx after_tx before_chain after_chain) :
      ReplayContentsSimple0 before_tx after_tx before_chain after_chain :=
    match h with
    | .mk _ _ _ _ _ _ h1 h2 => Relation.TransGen.head (.delete _ _ _ _ h1) h2.toSimple0

  theorem ReplayContentsStepAction.toSimple0 {before_tx after_tx : Tx} {before_chain after_chain : Chain}
      (h : ReplayContentsStepAction before_tx after_tx before_chain after_chain) :
      ReplayContentsSimple0 before_tx after_tx before_chain after_chain :=
    match h with
    | .mk _ _ _ _ _ _ h1 h2 => Relation.TransGen.head (.action _ _ _ _ h1) h2.toSimple0
end

theorem ReplayContents.ofSimple0 {p q : Tx × Chain}
    (h : Relation.TransGen (fun before after : Tx × Chain => ReplayElement before.1 after.1 before.2 after.2) p q) :
    ReplayContents p.1 q.1 p.2 q.2 := by
  induction h using Relation.TransGen.head_induction_on with
  | single h => exact .element _ _ _ _ h
  | head h1 _ ih =>
    match h1 with
    | .insert _ _ _ _ (.mk _ _ _ _ new new_live guard hh1 hh2 hh3 hh4) =>
      exact .insert _ _ _ _ (.mk _ _ _ _ _ _ ⟨new, new_live⟩ guard hh1 hh2 hh3 hh4 ih)
    | .mutate _ _ _ _ (.mk _ _ _ _ old new guard hh1 hh2 hh3) =>
      exact .mutate _ _ _ _ (.mk _ _ _ _ _ _ ⟨old, new⟩ guard hh1 hh2 hh3 ih)
    | .delete _ _ _ _ hd => exact .delete _ _ _ _ (.mk _ _ _ _ _ _ hd ih)
    | .action _ _ _ _ ha => exact .action _ _ _ _ (.mk _ _ _ _ _ _ ha ih)

theorem replayContents_iff_replayContentsSimple0 (before_tx after_tx : Tx) (before_chain after_chain : Chain) :
    ReplayContents before_tx after_tx before_chain after_chain ↔
      ReplayContentsSimple0 before_tx after_tx before_chain after_chain :=
  ⟨ReplayContents.toSimple0, ReplayContents.ofSimple0⟩

--
-- Stage 1
--

theorem ReplayContentsSimple.toTransGen {before_tx after_tx : Tx} {before_chain after_chain : Chain}
    (h : ReplayContentsSimple before_tx after_tx before_chain after_chain) :
    Relation.TransGen (fun before after : Tx × Chain => ReplayElementSimple before.1 after.1 before.2 after.2)
      (before_tx, before_chain) (after_tx, after_chain) :=
  match h with
  | .single _ _ _ _ h => Relation.TransGen.single h
  | .head _ _ _ _ _ _ h1 h2 => Relation.TransGen.head h1 h2.toTransGen

theorem ReplayContentsSimple.ofTransGen {p q : Tx × Chain}
    (h : Relation.TransGen (fun before after : Tx × Chain => ReplayElementSimple before.1 after.1 before.2 after.2) p q) :
    ReplayContentsSimple p.1 q.1 p.2 q.2 := by
  induction h using Relation.TransGen.head_induction_on with
  | single h => exact .single _ _ _ _ h
  | head h1 _ ih => exact .head _ _ _ _ _ _ h1 ih

-- TransGen bridge for ReplayContentsSimple which is defined as inductive following the same shape.
theorem replayContentsSimple_iff_transGen (before_tx after_tx : Tx) (before_chain after_chain : Chain) :
    ReplayContentsSimple before_tx after_tx before_chain after_chain ↔
      Relation.TransGen (fun before after : Tx × Chain => ReplayElementSimple before.1 after.1 before.2 after.2)
        (before_tx, before_chain) (after_tx, after_chain) :=
  ⟨ReplayContentsSimple.toTransGen, ReplayContentsSimple.ofTransGen⟩

-- Faithful → Stage-2 simple, for the whole replay cluster.
mutual
  theorem ReplayAction.toSimple {before_tx after_tx : Tx} {before_chain after_chain : Chain}
      (h : ReplayAction before_tx after_tx before_chain after_chain) :
      ReplayActionSimple before_tx after_tx before_chain after_chain :=
    match h with
    | .mk _ _ _ _ scope_mid inner_tx end_tx mid h1 h2 h3 h4 h5 =>
      .mk _ _ _ _ scope_mid inner_tx end_tx mid h1 h2 h3.toSimple h4 h5

  theorem ReplayContents.toSimple {before_tx after_tx : Tx} {before_chain after_chain : Chain}
      (h : ReplayContents before_tx after_tx before_chain after_chain) :
      ReplayContentsSimple before_tx after_tx before_chain after_chain :=
    match h with
    | .element _ _ _ _ h => .single _ _ _ _ h.toSimple
    | .insert _ _ _ _ h => h.toSimple
    | .mutate _ _ _ _ h => h.toSimple
    | .delete _ _ _ _ h => h.toSimple
    | .action _ _ _ _ h => h.toSimple

  theorem ReplayContentsStepInsert.toSimple {before_tx after_tx : Tx} {before_chain after_chain : Chain}
      (h : ReplayContentsStepInsert before_tx after_tx before_chain after_chain) :
      ReplayContentsSimple before_tx after_tx before_chain after_chain :=
    match h with
    | .mk _ _ _ _ _ _ ins guard h1 h2 h3 h4 h5 =>
      .head _ _ _ _ _ _
        (.insert _ _ _ _ (.mk _ _ _ _ ins.new ins.new_live guard h1 h2 h3 h4)) h5.toSimple

  theorem ReplayContentsStepMutate.toSimple {before_tx after_tx : Tx} {before_chain after_chain : Chain}
      (h : ReplayContentsStepMutate before_tx after_tx before_chain after_chain) :
      ReplayContentsSimple before_tx after_tx before_chain after_chain :=
    match h with
    | .mk _ _ _ _ _ _ pair guard h1 h2 h3 h4 =>
      .head _ _ _ _ _ _
        (.mutate _ _ _ _ (.mk _ _ _ _ pair.old pair.new guard h1 h2 h3)) h4.toSimple

  theorem ReplayContentsStepDelete.toSimple {before_tx after_tx : Tx} {before_chain after_chain : Chain}
      (h : ReplayContentsStepDelete before_tx after_tx before_chain after_chain) :
      ReplayContentsSimple before_tx after_tx before_chain after_chain :=
    match h with
    | .mk _ _ _ _ _ _ h1 h2 => .head _ _ _ _ _ _ (.delete _ _ _ _ h1) h2.toSimple

  theorem ReplayContentsStepAction.toSimple {before_tx after_tx : Tx} {before_chain after_chain : Chain}
      (h : ReplayContentsStepAction before_tx after_tx before_chain after_chain) :
      ReplayContentsSimple before_tx after_tx before_chain after_chain :=
    match h with
    | .mk _ _ _ _ _ _ h1 h2 => .head _ _ _ _ _ _ (.action _ _ _ _ h1.toSimple) h2.toSimple

  theorem ReplayElement.toSimple {before_tx after_tx : Tx} {before_chain after_chain : Chain}
      (h : ReplayElement before_tx after_tx before_chain after_chain) :
      ReplayElementSimple before_tx after_tx before_chain after_chain :=
    match h with
    | .insert _ _ _ _ h => .insert _ _ _ _ h
    | .mutate _ _ _ _ h => .mutate _ _ _ _ h
    | .delete _ _ _ _ h => .delete _ _ _ _ h
    | .action _ _ _ _ h => .action _ _ _ _ h.toSimple
end

-- Stage-2 simple → faithful.
mutual
  theorem ReplayActionSimple.toFaithful {before_tx after_tx : Tx} {before_chain after_chain : Chain}
      (h : ReplayActionSimple before_tx after_tx before_chain after_chain) :
      ReplayAction before_tx after_tx before_chain after_chain :=
    match h with
    | .mk _ _ _ _ scope_mid inner_tx end_tx mid h1 h2 h3 h4 h5 =>
      .mk _ _ _ _ scope_mid inner_tx end_tx mid h1 h2 h3.toFaithful h4 h5

  theorem ReplayElementSimple.toFaithful {before_tx after_tx : Tx} {before_chain after_chain : Chain}
      (h : ReplayElementSimple before_tx after_tx before_chain after_chain) :
      ReplayElement before_tx after_tx before_chain after_chain :=
    match h with
    | .insert _ _ _ _ h => .insert _ _ _ _ h
    | .mutate _ _ _ _ h => .mutate _ _ _ _ h
    | .delete _ _ _ _ h => .delete _ _ _ _ h
    | .action _ _ _ _ h => .action _ _ _ _ h.toFaithful

  theorem ReplayContentsSimple.toFaithful {before_tx after_tx : Tx} {before_chain after_chain : Chain}
      (h : ReplayContentsSimple before_tx after_tx before_chain after_chain) :
      ReplayContents before_tx after_tx before_chain after_chain :=
    match h with
    | .single _ _ _ _ h => .element _ _ _ _ h.toFaithful
    | .head _ _ _ _ _ _ h1 h2 =>
      match h1 with
      | .insert _ _ _ _ (.mk _ _ _ _ new new_live guard hh1 hh2 hh3 hh4) =>
        .insert _ _ _ _ (.mk _ _ _ _ _ _ ⟨new, new_live⟩ guard hh1 hh2 hh3 hh4 h2.toFaithful)
      | .mutate _ _ _ _ (.mk _ _ _ _ old new guard hh1 hh2 hh3) =>
        .mutate _ _ _ _ (.mk _ _ _ _ _ _ ⟨old, new⟩ guard hh1 hh2 hh3 h2.toFaithful)
      | .delete _ _ _ _ hd => .delete _ _ _ _ (.mk _ _ _ _ _ _ hd h2.toFaithful)
      | .action _ _ _ _ ha => .action _ _ _ _ (.mk _ _ _ _ _ _ ha.toFaithful h2.toFaithful)
end

theorem replayContentsSimple0_iff_replayContentsSimple (before_tx after_tx : Tx) (before_chain after_chain : Chain) :
    ReplayContentsSimple0 before_tx after_tx before_chain after_chain ↔
      ReplayContentsSimple before_tx after_tx before_chain after_chain :=
  ⟨fun h => (ReplayContents.ofSimple0 h).toSimple,
   fun h => h.toFaithful.toSimple0⟩

theorem replayActionsSimple0_iff_replayActionsSimple (before_tx after_tx : Tx) (before_chain after_chain : Chain) :
    ReplayActionsSimple0 before_tx after_tx before_chain after_chain ↔
      ReplayActionsSimple before_tx after_tx before_chain after_chain :=
  ⟨Relation.TransGen.mono (fun _ _ h => h.toSimple),
   Relation.TransGen.mono (fun _ _ h => h.toFaithful)⟩

theorem replayActions_iff_replayActionsSimple (before_tx after_tx : Tx) (before_chain after_chain : Chain) :
    ReplayActions before_tx after_tx before_chain after_chain ↔
      ReplayActionsSimple before_tx after_tx before_chain after_chain :=
  (replayActions_iff_replayActionsSimple0 before_tx after_tx before_chain after_chain).trans
    (replayActionsSimple0_iff_replayActionsSimple before_tx after_tx before_chain after_chain)

theorem txFinalized_iff_txFinalizedSimple (state_header : StateHeader) (tx_final : Tx) (nullifiers : Finset Nullifier) (live : Finset Object) :
    TxFinalized state_header tx_final nullifiers live ↔ TxFinalizedSimple state_header tx_final nullifiers live := by
  constructor
  · rintro ⟨before_tx, chain_start, chain_final, h1, h2, h3, ⟨hb1, hb2⟩, h5⟩
    exact .mk _ _ _ _ before_tx chain_start chain_final
      (InputsGrounded.toSimple0 h1) h2 h3 hb1 hb2
      ((replayActions_iff_replayActionsSimple _ _ _ _).mp h5)
  · rintro ⟨before_tx, chain_start, chain_final, h1, h2, h3, h4, h5, h6⟩
    exact .mk _ _ _ _ before_tx chain_start chain_final
      (InputsGrounded.ofSimple0 _ _ h1) h2 h3 (.mk _ _ _ h4 h5)
      ((replayActions_iff_replayActionsSimple _ _ _ _).mpr h6)

end TxLib
