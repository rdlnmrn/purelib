module

public import Purelib.Curves.Legendre.Paths
public import Purelib.Data.Rat.List.Minimum
import Purelib.Data.Fin.Cases
import Purelib.Data.Fin.Bijection.Basic
import Purelib.RootIsolation.Owner.Bridge.Basic
import Purelib.RootIsolation.Progressive.Chamber.Overlap
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.Polynomial.Clearance.Box.Boundary.Basic

/-!
# Common clearance of original Legendre chamber bridges

Each original bridge retains positive source and target boundary clearances.
Their finite labelled minima compute the common positive bound required by
the original segment owner, using the actual overlap bridge observations.
-/

public section

namespace Purelib.Curves.Legendre.Paths.BridgeClearance

open Purelib.Data
open Purelib.Data.Rat
open Fraction.Order

/-- Read the three original labelled bridges' paired endpoint clearance minima.

Each entry compares the actual source and target clearances of the same
retained overlap bridge. The original source frame's labels select its
original chamber indices. -/
@[expose] def bounds {start finish : Gaussian} (left : Frame start) (right : Frame finish)
    (overlap : ChamberOverlap left.chamber right.chamber) : List Coordinate :=
  let zero := overlap.bridge (left.labels.forward 0)
  let moving := overlap.bridge (left.labels.forward 1)
  let one := overlap.bridge (left.labels.forward 2)
  [min zero.leftClearance.bound zero.rightClearance.bound,
    min moving.leftClearance.bound moving.rightClearance.bound,
    min one.leftClearance.bound one.rightClearance.bound]

/-- Every paired clearance observation of the same original overlap is positive. -/
theorem bounds_positive {start finish : Gaussian} (left : Frame start) (right : Frame finish)
    (overlap : ChamberOverlap left.chamber right.chamber) (value : Coordinate)
    (member : value ∈ bounds left right overlap) : 0 < value := by
  cases member with
  | head =>
      exact Basic.lt_min (overlap.bridge (left.labels.forward 0)).leftClearance.positive
        (overlap.bridge (left.labels.forward 0)).rightClearance.positive
  | tail _ tail =>
      cases tail with
      | head =>
          exact Basic.lt_min (overlap.bridge (left.labels.forward 1)).leftClearance.positive
            (overlap.bridge (left.labels.forward 1)).rightClearance.positive
      | tail _ tail =>
          cases tail with
          | head =>
              exact Basic.lt_min (overlap.bridge (left.labels.forward 2)).leftClearance.positive
                (overlap.bridge (left.labels.forward 2)).rightClearance.positive
          | tail _ empty => cases empty

/-- Every original labelled bridge's paired endpoint minimum belongs to the same observed clearance list. -/
theorem bounds_member {start finish : Gaussian} (left : Frame start) (right : Frame finish)
    (overlap : ChamberOverlap left.chamber right.chamber) (label : Fin 3) :
    min (overlap.bridge (left.labels.forward label)).leftClearance.bound
      (overlap.bridge (left.labels.forward label)).rightClearance.bound ∈ bounds left right overlap := by
  rcases Fin.Cases.three label with zero | moving | one
  · subst label
    exact List.Mem.head _
  · subst label
    exact List.Mem.tail _ (List.Mem.head _)
  · subst label
    exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

/-- Compute the original common bridge-clearance certificate from an actual complete chamber overlap.

The same observed endpoint minima are folded once into a positive bound.
The original source-label bijection locates every chamber index in that
retained list, whose minimum pays both clearances of the same bridge. -/
@[expose] def ofOverlap {start finish : Gaussian} (left : Frame start) (right : Frame finish)
    (overlap : ChamberOverlap left.chamber right.chamber) : BridgeClearance left right overlap := by
  let observed := bounds left right overlap
  let bound := List.Minimum.positiveMinimum observed
  have lower (index : left.chamber.Index) :
      bound ≤ min (overlap.bridge index).leftClearance.bound (overlap.bridge index).rightClearance.bound := by
    have paid := List.Minimum.positiveMinimum_le_of_mem (bounds_member left right overlap (left.labels.backward index))
    rewrite [left.labels.forward_backward] at paid
    exact paid
  exact
    { bound := bound
      positive := List.Minimum.positiveMinimum_pos observed (bounds_positive left right overlap)
      leftLower := fun index => (lower index).trans (Basic.min_le_left _ _)
      rightLower := fun index => (lower index).trans (Basic.min_le_right _ _) }

/-- The computed common clearance is the minimum of the same retained original bridge observations. -/
theorem ofOverlap_bound {start finish : Gaussian} (left : Frame start) (right : Frame finish)
    (overlap : ChamberOverlap left.chamber right.chamber) :
    (ofOverlap left right overlap).bound = List.Minimum.positiveMinimum (bounds left right overlap) := rfl

end Purelib.Curves.Legendre.Paths.BridgeClearance
