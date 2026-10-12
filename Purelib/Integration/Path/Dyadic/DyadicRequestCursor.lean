module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Append
import Purelib.Data.List.Membership
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Riemann.Branches.ClearSheetContinuation

public import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Tactic.QuotientFreeOmega

section
public section

/-!
Expose the original ordered dyadic requests one at a time. A finite stack
retains every unvisited interval; its interpretation is exactly the original
list. The interpretation occurs only in certificates during incremental scans.
-/

namespace Purelib.Integration.Path.Dyadic.DyadicRequestCursor

open Purelib

open Purelib.Riemann
open Purelib.Riemann.Branches

open PreparedSheetContinuation (Coordinate Endpoint StepRequest)
open ClearSheetContinuation (midpoint midpoint_inside)
open ClearSheetContinuation.Subdivision (dyadicTargets dyadicTargets_length)
open PreparedSheetContinuation.Subdivision (requestsAtDiameter requestsAtDiameter_length)

set_option genInjectivity false in
/-- A retained subdivision depth and two exact continuation endpoint owners. -/
structure Frame where
  /-- The retained subdivision depth of this pending frame. -/ depth : Nat
  /-- The exact original left continuation endpoint and its interval witness. -/ left : Endpoint
  /-- The exact original right continuation endpoint and its interval witness. -/ right : Endpoint

constructive_injectivity Frame

/-- The ordered stack of retained dyadic request frames. -/
abbrev Cursor := List Integration.Path.Dyadic.DyadicRequestCursor.Frame

/-- Expand the exact pending frame stack into its ordered original target endpoints. -/
@[expose] def endpoints : Integration.Path.Dyadic.DyadicRequestCursor.Cursor → List Endpoint
  | [] => []
  | frame :: rest => dyadicTargets frame.depth frame.left frame.right ++
    Purelib.Integration.Path.Dyadic.DyadicRequestCursor.endpoints rest

/-- Count the pending target endpoints by summing two to each retained frame depth. -/
@[expose] def count : Integration.Path.Dyadic.DyadicRequestCursor.Cursor → Nat
  | [] => 0
  | frame :: rest => 2 ^ frame.depth + Purelib.Integration.Path.Dyadic.DyadicRequestCursor.count rest

/-- Read the exact pending cursor endpoints as continuation requests at the supplied positive root diameter. -/
@[expose] def requests (diameter : Coordinate) (positive : 0 < diameter) (cursor :
  Integration.Path.Dyadic.DyadicRequestCursor.Cursor) : List StepRequest :=
  requestsAtDiameter diameter positive (Integration.Path.Dyadic.DyadicRequestCursor.endpoints cursor)

/-- The retained request list has length equal to the cursor's exact pending count. -/
theorem requests_length (diameter : Coordinate) (positive : 0 < diameter) (cursor :
  Integration.Path.Dyadic.DyadicRequestCursor.Cursor) :
    (Integration.Path.Dyadic.DyadicRequestCursor.requests diameter positive cursor).length =
      Integration.Path.Dyadic.DyadicRequestCursor.count cursor := by
  rw [Integration.Path.Dyadic.DyadicRequestCursor.requests, requestsAtDiameter_length]
  induction cursor with
  | nil => rfl
  | cons frame rest ih =>
      simp only [Integration.Path.Dyadic.DyadicRequestCursor.endpoints, Data.List.Append.length_append,
        dyadicTargets_length, Integration.Path.Dyadic.DyadicRequestCursor.count, ih, -eq_self]
      rfl

set_option genInjectivity false in
/-- One retained next request and remaining cursor with an exact original request-list decomposition. -/
structure Head (diameter : Coordinate) (positive : 0 < diameter) (cursor :
  Integration.Path.Dyadic.DyadicRequestCursor.Cursor) where
  /-- The retained next continuation request at the original diameter. -/ request : StepRequest
  /-- The retained cursor for the exact remaining requests. -/ remaining :
    Integration.Path.Dyadic.DyadicRequestCursor.Cursor
  /-- The original request stream is this request followed by the exact remaining cursor's stream. -/ equation :
    Integration.Path.Dyadic.DyadicRequestCursor.requests diameter positive cursor = request ::
    Integration.Path.Dyadic.DyadicRequestCursor.requests diameter positive remaining

constructive_injectivity Head

/-- Descend the first retained dyadic frame to expose its next request while retaining the remaining frames.

Each subdivision preserves the exact endpoint witnesses and requested diameter; the returned decomposition links this
head and remaining cursor to the original request stream. -/
@[expose] def expose (diameter : Coordinate) (positive : 0 < diameter) :
    (depth : Nat) → (left right : Endpoint) → (rest : Integration.Path.Dyadic.DyadicRequestCursor.Cursor) →
      Integration.Path.Dyadic.DyadicRequestCursor.Head diameter positive (⟨depth, left, right⟩ :: rest)
  | 0, _, right, rest => ⟨⟨right, diameter, positive⟩, rest, rfl⟩
  | depth + 1, left, right, rest =>
      let middle : Endpoint := ⟨midpoint left.parameter right.parameter,
        midpoint_inside left.inside right.inside⟩
      let head := Purelib.Integration.Path.Dyadic.DyadicRequestCursor.expose diameter positive depth left middle
        (⟨depth, middle, right⟩ :: rest)
      ⟨head.request, head.remaining, by
        change requestsAtDiameter diameter positive
          ((dyadicTargets depth left middle ++ dyadicTargets depth middle right) ++
            Integration.Path.Dyadic.DyadicRequestCursor.endpoints rest) = _
        rw [Data.List.Append.append_assoc]
        exact head.equation⟩

/-- The remaining cursor count plus its removed head equals the original count.

The retained request-list decomposition identifies one request followed by the
remaining cursor's exact request stream at the same positive diameter. -/
@[simp] theorem Head.count_remaining {diameter positive cursor}
    (head : Head diameter positive cursor) :
    count head.remaining + 1 = count cursor :=
  ((congrArg Nat.succ (requests_length diameter positive head.remaining)).symm.trans
    ((congrArg List.length head.equation).symm)).trans
      (requests_length diameter positive cursor)

/-- Removing the retained head request strictly decreases the exact pending cursor count. -/
theorem Head.decreases {diameter positive cursor} (head : Integration.Path.Dyadic.DyadicRequestCursor.Head diameter
  positive cursor) :
    Integration.Path.Dyadic.DyadicRequestCursor.count head.remaining < Integration.Path.Dyadic.DyadicRequestCursor.count
      cursor := by
  have lengths := congrArg List.length head.equation
  simp only [List.length_cons, Integration.Path.Dyadic.DyadicRequestCursor.requests_length] at lengths
  omega

/-- The exposed request retains the original cursor request's exact root diameter. -/
theorem Head.rootDiameter_eq {diameter positive cursor} (head : Integration.Path.Dyadic.DyadicRequestCursor.Head
  diameter positive cursor) :
    head.request.rootDiameter = diameter := by
  have member : head.request ∈ Integration.Path.Dyadic.DyadicRequestCursor.requests diameter positive cursor := by
    rw [head.equation]
    exact List.Mem.head _
  have fixed : ∀ values, ∀ request ∈ requestsAtDiameter diameter positive values,
      request.rootDiameter = diameter := by
    intro values
    induction values with
    | nil => intro request member; cases member
    | cons endpoint remaining ih =>
        intro request member
        rcases Data.List.Membership.mem_cons.mp member with same | later
        · cases same
          rfl
        · exact ih request later
  exact fixed _ _ member

/-- Create a one-frame cursor for the original depth and endpoint owners. -/
@[expose] def initial (depth : Nat) (left right : Endpoint) : Integration.Path.Dyadic.DyadicRequestCursor.Cursor :=
  [⟨depth, left, right⟩]

/-- The initial cursor's requests are exactly the original canonical dyadic requests. -/
theorem initial_eq (depth : Nat) (left right : Endpoint)
    (diameter : Coordinate) (positive : 0 < diameter) :
    Integration.Path.Dyadic.DyadicRequestCursor.requests diameter positive
      (Integration.Path.Dyadic.DyadicRequestCursor.initial depth left right) =
      PreparedSheetContinuation.Subdivision.dyadicRequests depth left right diameter positive := by
  simp only [Integration.Path.Dyadic.DyadicRequestCursor.requests, Integration.Path.Dyadic.DyadicRequestCursor.initial,
    Integration.Path.Dyadic.DyadicRequestCursor.endpoints, Data.List.Append.append_nil,
    PreparedSheetContinuation.Subdivision.dyadicRequests, -eq_self]
  rfl

end Purelib.Integration.Path.Dyadic.DyadicRequestCursor

end

public section

/-!
The first-endpoint and finite-prefix operations retain the original endpoint
owners while evaluating only the requested dyadic subtree. Their certificates
identify the exact head and take of the same canonical target list.
-/

namespace Purelib.Integration.Path.Dyadic.DyadicRequestCursor

open Purelib.Riemann.Branches.PreparedSheetContinuation (Endpoint StepRequest)
open Purelib.Curves.Hyperelliptic.Branches.Cuts
  (connectorAt_start_eval_ne_zero connectorAt_finish_eval_ne_zero)

/-- Descend the original leftmost subdivision branch to its first target endpoint. -/
@[expose] def firstDyadicEndpoint : Nat → Endpoint → Endpoint → Endpoint
  | 0, _, right => right
  | depth + 1, left, right => Purelib.Integration.Path.Dyadic.DyadicRequestCursor.firstDyadicEndpoint depth left
      ⟨Purelib.Riemann.Branches.ClearSheetContinuation.midpoint left.parameter right.parameter,
        Purelib.Riemann.Branches.ClearSheetContinuation.midpoint_inside left.inside right.inside⟩

/-- The first target of the original dyadic endpoint list is the directly selected endpoint. -/
theorem firstDyadicEndpoint_eq (depth : Nat) (left right : Endpoint) :
    (Riemann.Branches.ClearSheetContinuation.Subdivision.dyadicTargets depth left right).head? =
      some (Integration.Path.Dyadic.DyadicRequestCursor.firstDyadicEndpoint depth left right) := by
  induction depth generalizing left right with
  | zero => rfl
  | succ depth ih =>
      rw [Riemann.Branches.ClearSheetContinuation.Subdivision.dyadicTargets, Data.List.Append.head?_append, ih]
      rfl

/-- Compute the requested initial prefix of original dyadic target endpoints without expanding the unused suffix.

The recursion retains the original endpoints and subtracts the exact left-subtree size before visiting a needed right
subtree. -/
@[expose] def firstDyadicEndpoints : Nat → Nat → Endpoint → Endpoint → List Endpoint
  | _, 0, _, _ => []
  | 0, _ + 1, _, right => [right]
  | depth + 1, count + 1, left, right =>
      let middle : Endpoint :=
        ⟨Riemann.Branches.ClearSheetContinuation.midpoint left.parameter right.parameter,
          Riemann.Branches.ClearSheetContinuation.midpoint_inside left.inside right.inside⟩
      Purelib.Integration.Path.Dyadic.DyadicRequestCursor.firstDyadicEndpoints depth (count + 1) left middle ++
        Purelib.Integration.Path.Dyadic.DyadicRequestCursor.firstDyadicEndpoints depth (count + 1 - 2 ^ depth) middle
          right

/-- The directly computed original endpoint prefix equals taking that count from the canonical target list. -/
theorem firstDyadicEndpoints_eq (depth count : Nat) (left right : Endpoint) :
    Integration.Path.Dyadic.DyadicRequestCursor.firstDyadicEndpoints depth count left right =
      (Riemann.Branches.ClearSheetContinuation.Subdivision.dyadicTargets depth left right).take count := by
  induction depth generalizing count left right with
  | zero =>
      cases count with
      | zero => rfl
      | succ count =>
          simp only [Integration.Path.Dyadic.DyadicRequestCursor.firstDyadicEndpoints,
            Riemann.Branches.ClearSheetContinuation.Subdivision.dyadicTargets,
            List.take_succ_cons, List.take_nil, -eq_self]
          rfl
  | succ depth ih =>
      cases count with
      | zero => rfl
      | succ count =>
          rw [Integration.Path.Dyadic.DyadicRequestCursor.firstDyadicEndpoints,
            Riemann.Branches.ClearSheetContinuation.Subdivision.dyadicTargets,
            Data.List.Append.take_append_direct,
              Riemann.Branches.ClearSheetContinuation.Subdivision.dyadicTargets_length,
            ih, ih]
end Purelib.Integration.Path.Dyadic.DyadicRequestCursor

end
