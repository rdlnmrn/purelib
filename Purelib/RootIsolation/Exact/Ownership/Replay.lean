module
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.Exact.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.Exact.Ownership.Basic
public import Purelib.RootIsolation.Exact.Ownership.Prepare
import Purelib.RootIsolation.Exact.Ownership.Radius
import Purelib.RootIsolation.Exact.Partition.Location
import Purelib.RootIsolation.Exact.Partition.Margin
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.State.WindingOne.Count
import Purelib.RootIsolation.State.WindingOne.Interior
import Purelib.RootIsolation.Track.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-! Restore the original partition classification from its exact refined state. -/
namespace Purelib.RootIsolation.Exact.Ownership.Replay

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {count
  degreeBound : Nat}
  (degreeAtLeastTwo : 2 ≤ p.natDegree) (squarefree :
    Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
  (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound) (output :
    Exact.Basic.Output p ambient count)
  (track : Track.Basic.WindingOneTrack p ambient) (supported : track.initial.box.Refines
    output.support)

/-- A cached state equal to the original track's refinement at the partition ownership radius. -/
abbrev Refined := {state :
  State.WindingOne.Basic.WindingOneState p ambient // state =
  track.refine track.initial (Exact.Ownership.Radius.assignmentRadius p ambient output)
    (Exact.Ownership.Radius.assignmentRadius_pos p ambient output)}

/-- Restore the original owner selection using the checked cached ownership-radius refinement.

Locate the saved state's anchor in the original partition and retain strict owner containment; the source track, radius
and refined state remain linked by the saved equality. -/
def restore (saved : Refined output track) :
  Exact.Ownership.Basic.OwnerSelection output track := by
  let radius := Exact.Ownership.Radius.assignmentRadius p ambient output
  let radiusPositive := Exact.Ownership.Radius.assignmentRadius_pos p ambient output
  let refined := saved.val
  have refinedEq : refined = track.refine track.initial radius radiusPositive := saved.property
  have refinedSupport : refined.box.Refines output.support :=
    by
    rw [refinedEq]
    exact (track.nested track.initial radius radiusPositive).trans supported
  have anchorSupport : output.support.Contains refined.box.anchor :=
    refinedSupport.contains refined.box.contains_anchor
  let location := Exact.Partition.Location.locatePartition output refined.box.anchor anchorSupport
  have anchorCell : location.box.Contains refined.box.anchor :=
    Exact.Partition.Location.locatePartition_contains output refined.box.anchor anchorSupport
  have diagonal : refined.box.diagonalSq ≤ radius ^ 2 :=
by
    rw [refinedEq]
    exact track.accurate track.initial radius radiusPositive
  have degreePositive : 0 < p.natDegree :=
    (show (0 : Nat) < 2 by decide).trans_le degreeAtLeastTwo
  cases locationEq : location with
  | track index =>
      have anchorTrack : (output.tracks.get index).initial.box.Contains
          refined.box.anchor := by
        simpa only [locationEq, Exact.Partition.Location.PartitionLocation.box] using anchorCell
      have strict : refined.box.StrictInterior
          (output.tracks.get index).initial.box :=
        State.WindingOne.Interior.strictInterior_of_anchor_mem_of_dominates p refined degreePositive
          (output.tracks.get index).initial.refinesAmbient
          (output.tracks.get index).initial.clearance anchorTrack
          (Exact.Ownership.Radius.assignment_dominates p ambient output refined diagonal
            (Exact.Partition.Margin.partitionMargin_le_track output index))
      exact ⟨index, by
        change (track.refine track.initial radius radiusPositive).box.StrictInterior _
        rw [← refinedEq]
        exact strict⟩
  | remainder index =>
      let region := output.remainder.get index
      have anchorRegion : region.box.Contains refined.box.anchor := by
        simpa only [region, locationEq, Exact.Partition.Location.PartitionLocation.box] using anchorCell
      have strict : refined.box.StrictInterior region.box :=
        State.WindingOne.Interior.strictInterior_of_anchor_mem_of_dominates p refined degreePositive
          region.refinesAmbient region.clearance anchorRegion
          (Exact.Ownership.Radius.assignment_dominates p ambient output refined diagonal
            (Exact.Partition.Margin.partitionMargin_le_remainder output index))
      have atLeastFour := State.WindingOne.Count.region_rawWinding_ge_four_of_strictInterior
        degreeAtLeastTwo squarefree elimination refined region strict
      have zero := output.remainder_rawWinding_zero region
        (List.get_mem output.remainder index)
      exact (by omega : False).elim

/-- Restoring the checked refinement cache returns exactly the original deterministic owner selection. -/
theorem restore_eq (saved : Refined output
  track) :
    restore degreeAtLeastTwo squarefree elimination output track supported saved =
      Exact.Ownership.Prepare.selectOutputOwner degreeAtLeastTwo squarefree elimination output track supported := by
  rcases saved with ⟨state, same⟩
  cases same
  rfl

end Purelib.RootIsolation.Exact.Ownership.Replay

end
