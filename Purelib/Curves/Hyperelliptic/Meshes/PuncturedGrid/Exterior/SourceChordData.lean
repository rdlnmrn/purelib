module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Algebra.Group.Negation
import Purelib.Data.List.OfFn.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisInterval
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.SourceIntervals
import Purelib.Integration.Path.CenteredPathIncrements
import Purelib.Integration.Path.Dyadic.DyadicTrace
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Init.Data.List.OfFn
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryFragmentArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceComparison
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Data.Rat

open Purelib.Geometry.Rectangle

open Purelib.Geometry.Rectangle.Partition

open Purelib.Integration.Path

open Purelib.Integration.Path.Dyadic

open Purelib.Riemann.Paths

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

public section

/-! Retain each canonical source fragment with its closed-bank parent,
parameter interval and cached fine sample. Its endpoint chord certifies the
total, while the fine increments retain the full internal excursion area. -/
section
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfacePreparation SurfaceOccurrence)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms (ExteriorProgram)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryAxisInterval (ParentInterval)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters (firstParameter lastParameter
  parent_parameter_eq parent_signed_bounds parent_signed_parameter_eq)
open Purelib.Riemann.Paths.RectangularDyadicPairedTrace (dyadicCount)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters (signedAxis)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks (maximum maximum_nonnegative
  le_maximum)
open Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint (Bounded)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Geometry.Rectangle.SourceIntervals (axisCoordinate)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential other :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {program : ExteriorProgram lifted
    differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}
  {requested : Coordinate} {minimum : Nat}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

namespace SourceChordData

/-- The original retained parent's paired primitive displacement across the direction-selected parameter interval. -/
@[expose] def chordValue (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (index : Fin comparison.original.plans.length) (forward : Bool) (range : PreparedAxisPartitions.Interval) :
      PrimitivePoint :=
  (comparison.sourceValues index (BoundaryTraceParameters.lastParameter forward range)).sub
    (comparison.sourceValues index (BoundaryTraceParameters.firstParameter forward range))

/-- Map the original unit dyadic mesh into the retained parent interval in the selected direction. -/
@[expose] def sourceParameters (forward : Bool) (range : PreparedAxisPartitions.Interval) (depth : Nat)
    (vertex : Fin (RectangularDyadicPairedTrace.dyadicCount depth + 1)) : Coordinate :=
  BoundaryTraceParameters.firstParameter forward range +
    DyadicTrace.indexed 0
      (DyadicTrace.tail depth 0 1) vertex *
        (BoundaryTraceParameters.lastParameter forward range - BoundaryTraceParameters.firstParameter forward range)

/-- A centered sample of the exact original closed-bank source values at the retained interval's dyadic parameters. -/
@[expose] def SourceSample (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (index : Fin comparison.original.plans.length) (forward : Bool)
    (range : PreparedAxisPartitions.Interval) (depth : Nat) :=
  CenteredBilinearPath.Sample
    (fun vertex => comparison.sourceValues index
      (sourceParameters forward range depth vertex))

/-- The first source sample parameter is the retained direction-selected interval start. -/
theorem sourceParameters_first (forward : Bool) (range : PreparedAxisPartitions.Interval) (depth : Nat) :
    sourceParameters forward range depth 0 =
      BoundaryTraceParameters.firstParameter forward range := by
  dsimp only [sourceParameters,
    DyadicTrace.indexed_first, -eq_self, -iff_self]
  ring1

/-- The last source sample parameter is the retained direction-selected interval finish. -/
theorem sourceParameters_last (forward : Bool) (range : PreparedAxisPartitions.Interval) (depth : Nat) :
    sourceParameters forward range depth
      (Fin.last (RectangularDyadicPairedTrace.dyadicCount depth)) = BoundaryTraceParameters.lastParameter forward range
        := by
  dsimp only [sourceParameters, -eq_self, -iff_self]
  rw [DyadicTrace.indexed_last,
    DyadicTrace.tail_terminal]
  ring1

end SourceChordData

set_option genInjectivity false in
/-- A cached source fragment retaining its original closed-bank parent, oriented unit subinterval, endpoint chord and
full dyadic sample.

The axis certificates identify the physical interval while the sample preserves all internal increments and excursion
area. -/
structure SourceChordData (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (vertical : Bool) (physical : PreparedAxisPartitions.Interval) where
  /-- The exact original source parent position in the closed comparison bank. -/ index : Fin
    comparison.original.plans.length
  /-- The retained direction of the source parameter traversal. -/ forward : Bool
  /-- The original proper source parameter subinterval. -/ range : PreparedAxisPartitions.Interval
  /-- Both retained source subinterval endpoints lie in the unit parent interval. -/ within : 0 ≤ range.lower ∧
    range.upper ≤ 1
  /-- The cached paired primitive endpoint chord of this original source fragment. -/ value : Stokes.PrimitivePoint
  /-- The cached chord is the exact displacement of the retained source owner at its selected endpoints. -/ value_eq :
    value = Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordData.chordValue comparison index forward range
  /-- The original parent is strictly increasing in the retained signed axis. -/ ordered :
    SourceBlockParameters.signedAxis vertical forward ((comparison.Parent index).edge.point 0) <
    SourceBlockParameters.signedAxis vertical forward ((comparison.Parent index).edge.point 1)
  /-- The first retained source parameter reads the physical interval's lower coordinate. -/ first_axis :
    SourceIntervals.axisCoordinate vertical
    ((comparison.Parent index).edge.point (BoundaryTraceParameters.firstParameter forward range)) = physical.lower
  /-- The last retained source parameter reads the physical interval's upper coordinate. -/ last_axis :
    SourceIntervals.axisCoordinate vertical
    ((comparison.Parent index).edge.point (BoundaryTraceParameters.lastParameter forward range)) = physical.upper
  /-- The retained dyadic sampling depth of this exact source fragment. -/ depth : Nat
  /-- The cached centered sample on the original parent and retained parameter interval. -/ sample :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordData.SourceSample comparison index forward range depth

constructive_injectivity SourceChordData

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordData

/-- Cache the original selected parent, oriented parameter interval, exact endpoint chord and complete dyadic source
sample. -/
@[expose] def build (comparison : prepared.ClosedBoundaryComparison other requested minimum)
    (index : Fin comparison.original.plans.length) (forward vertical : Bool) (physical :
      PreparedAxisPartitions.Interval)
    (range : BoundaryAxisInterval.ParentInterval (comparison.Parent index) vertical physical)
    (ordered : SourceBlockParameters.signedAxis vertical forward ((comparison.Parent index).edge.point 0) <
      SourceBlockParameters.signedAxis vertical forward ((comparison.Parent index).edge.point 1))
    (depth : Nat) : SourceChordData comparison
      vertical physical :=
  ⟨index, forward, range.val, range.property.1,
    chordValue comparison index forward range.val,
    rfl,
    ordered, (range.endpoint_axes ordered).1, (range.endpoint_axes ordered).2, depth,
    CenteredBilinearPath.Sample.build _⟩

/-- Read the complete original increment path from the cached source sample. -/
@[expose] def increments {comparison : prepared.ClosedBoundaryComparison other requested minimum}
    {vertical : Bool} {physical : PreparedAxisPartitions.Interval}
    (chord : SourceChordData comparison vertical
      physical) := CenteredPathIncrements.Sample.increments chord.sample

/-- The complete retained source increment path has exactly the cached endpoint chord as its total. -/
theorem increments_total {comparison : prepared.ClosedBoundaryComparison other requested minimum}
    {vertical : Bool} {physical : PreparedAxisPartitions.Interval}
    (chord : SourceChordData comparison vertical
      physical) :
    PairedIncrementArea.total chord.increments = chord.value := by
  exact (CenteredPathIncrements.Sample.increments_total chord.sample).trans ((congrArg₂ PrimitivePoint.sub
    (congrArg (comparison.sourceValues chord.index)
      (sourceParameters_last ..))
    (congrArg (comparison.sourceValues chord.index)
      (sourceParameters_first ..))).trans
      chord.value_eq.symm)

/-- Consecutive physical intervals on the identical original source parent have equal adjoining source parameters. -/
theorem same_parent_parameters {comparison : prepared.ClosedBoundaryComparison other requested minimum}
    {vertical : Bool} {beforePhysical afterPhysical : PreparedAxisPartitions.Interval}
    (before : SourceChordData comparison vertical
      beforePhysical) (after : SourceChordData
      comparison vertical afterPhysical)
    (same : after.index = before.index) (consecutive : afterPhysical.lower = beforePhysical.upper) :
    BoundaryTraceParameters.firstParameter after.forward after.range = BoundaryTraceParameters.lastParameter
      before.forward before.range := by
  have equal := after.first_axis.trans (consecutive.trans before.last_axis.symm)
  rw [same] at equal
  exact BoundaryTraceParameters.parent_parameter_eq before.ordered equal

/-- Only a junction within the same retained source parent cancels exactly. No equality between distinct parents'
primitive owners is asserted. -/
theorem same_parent_join {comparison : prepared.ClosedBoundaryComparison other requested minimum}
    {vertical : Bool} {beforePhysical afterPhysical : PreparedAxisPartitions.Interval}
    (before : SourceChordData comparison vertical
      beforePhysical) (after : SourceChordData
      comparison vertical afterPhysical)
    (same : after.index = before.index) (consecutive : afterPhysical.lower = beforePhysical.upper) :
    (comparison.sourceValues after.index (BoundaryTraceParameters.firstParameter after.forward after.range)).sub
      (comparison.sourceValues before.index (BoundaryTraceParameters.lastParameter before.forward before.range)) =
        PrimitivePoint.zero := by
  have parameters := before.same_parent_parameters after same consecutive
  rw [same, parameters]
  apply congrArg₂ PrimitivePoint.mk <;> exact sub_self _

/-- Disjoint source parents meeting at a physical junction can meet only at their full parent endpoints; the primitive
values themselves may differ. -/
theorem cross_parent_endpoints {comparison : prepared.ClosedBoundaryComparison other requested minimum}
    {vertical : Bool} {beforePhysical afterPhysical : PreparedAxisPartitions.Interval}
    (before : SourceChordData comparison vertical
      beforePhysical) (after : SourceChordData
      comparison vertical afterPhysical)
    (forward : Bool) (beforeForward : before.forward = forward) (afterForward : after.forward = forward)
    (consecutive : afterPhysical.lower = beforePhysical.upper)
    (separated : if forward then
      SourceBlockParameters.signedAxis vertical forward ((comparison.Parent before.index).edge.point 1) ≤
        SourceBlockParameters.signedAxis vertical forward ((comparison.Parent after.index).edge.point 0)
      else SourceBlockParameters.signedAxis vertical forward ((comparison.Parent after.index).edge.point 1) ≤
        SourceBlockParameters.signedAxis vertical forward ((comparison.Parent before.index).edge.point 0)) :
    BoundaryTraceParameters.lastParameter before.forward before.range = (if forward then 1 else 0) ∧
      BoundaryTraceParameters.firstParameter after.forward after.range = (if forward then 0 else 1) := by
  have beforeInside : 0 ≤ BoundaryTraceParameters.lastParameter before.forward before.range ∧
    BoundaryTraceParameters.lastParameter before.forward before.range ≤ 1 := by
    cases before.forward with
    | true => exact ⟨before.within.1.trans before.range.ordered.le, before.within.2⟩
    | false => exact ⟨before.within.1, before.range.ordered.le.trans before.within.2⟩
  have afterInside : 0 ≤ BoundaryTraceParameters.firstParameter after.forward after.range ∧
    BoundaryTraceParameters.firstParameter after.forward after.range ≤ 1 := by
    cases after.forward with
    | true => exact ⟨after.within.1, after.range.ordered.le.trans after.within.2⟩
    | false => exact ⟨after.within.1.trans after.range.ordered.le, after.within.2⟩
  have left := BoundaryTraceParameters.parent_signed_bounds before.ordered beforeInside
  have right := BoundaryTraceParameters.parent_signed_bounds after.ordered afterInside
  have joint := after.first_axis.trans (consecutive.trans before.last_axis.symm)
  rw [beforeForward, afterForward] at joint ⊢
  cases forward with
  | true =>
    simp only [beforeForward, afterForward, SourceBlockParameters.signedAxis, if_pos (show (true : Bool) = true from
      rfl), -eq_self, -iff_self] at left right separated
    have endpoints := And.intro
      (le_antisymm left.2 ((separated.trans right.1).trans_eq joint))
      (le_antisymm (joint.trans_le (left.2.trans separated)) right.1)
    exact ⟨parent_parameter_eq before.ordered endpoints.1, BoundaryTraceParameters.parent_parameter_eq after.ordered
      endpoints.2⟩
  | false =>
    simp only [beforeForward, afterForward, SourceBlockParameters.signedAxis, if_neg (show (false : Bool) ≠ true from
      Bool.noConfusion), -eq_self, -iff_self] at left right separated
    have leftOrder := (Fraction.Order.Arithmetic.neg_le_neg_iff_direct _ _).mp left.1
    have gapOrder := (Fraction.Order.Arithmetic.neg_le_neg_iff_direct _ _).mp separated
    have rightOrder := (Fraction.Order.Arithmetic.neg_le_neg_iff_direct _ _).mp right.2
    have endpoints := And.intro
      (le_antisymm leftOrder ((gapOrder.trans rightOrder).trans_eq joint))
      (le_antisymm (joint.trans_le (leftOrder.trans gapOrder)) rightOrder)
    exact ⟨parent_parameter_eq before.ordered endpoints.1, BoundaryTraceParameters.parent_parameter_eq after.ordered
      endpoints.2⟩

/-- Retained consecutive physical intervals meeting at full parent endpoints have the exact signed parent-junction
equality. -/
theorem parent_junction {comparison : prepared.ClosedBoundaryComparison other requested minimum}
    {vertical : Bool} {beforePhysical afterPhysical : PreparedAxisPartitions.Interval}
    (before : SourceChordData comparison vertical
      beforePhysical) (after : SourceChordData
      comparison vertical afterPhysical)
    (forward : Bool) (consecutive : afterPhysical.lower = beforePhysical.upper)
    (endpoints : BoundaryTraceParameters.lastParameter before.forward before.range = (if forward then 1 else 0) ∧
      BoundaryTraceParameters.firstParameter after.forward after.range = (if forward then 0 else 1)) :
    if forward then
      SourceBlockParameters.signedAxis vertical forward ((comparison.Parent before.index).edge.point 1) =
        SourceBlockParameters.signedAxis vertical forward ((comparison.Parent after.index).edge.point 0)
    else
      SourceBlockParameters.signedAxis vertical forward ((comparison.Parent after.index).edge.point 1) =
        SourceBlockParameters.signedAxis vertical forward ((comparison.Parent before.index).edge.point 0) := by
  have joint := after.first_axis.trans (consecutive.trans before.last_axis.symm)
  rw [endpoints.1, endpoints.2] at joint
  cases forward with
  | true => exact joint.symm
  | false => exact congrArg Neg.neg joint

/-- Physical side endpoint alignment and original parent-span bounds determine the complete source run's terminal
parameters. -/
theorem side_endpoints {comparison : prepared.ClosedBoundaryComparison other requested minimum}
    {vertical : Bool} {firstPhysical lastPhysical : PreparedAxisPartitions.Interval}
    (first : SourceChordData comparison vertical
      firstPhysical) (last : SourceChordData
      comparison vertical lastPhysical)
    (forward : Bool) (firstForward : first.forward = forward) (lastForward : last.forward = forward)
    {start finish : InverseRootPolynomial.Coordinate}
    (firstBounds : start ≤ SourceBlockParameters.signedAxis vertical forward ((comparison.Parent first.index).edge.point
      0) ∧
      SourceBlockParameters.signedAxis vertical forward ((comparison.Parent first.index).edge.point 1) ≤ finish)
    (lastBounds : start ≤ SourceBlockParameters.signedAxis vertical forward ((comparison.Parent last.index).edge.point
      0) ∧
      SourceBlockParameters.signedAxis vertical forward ((comparison.Parent last.index).edge.point 1) ≤ finish)
    (startEq : (if forward then firstPhysical.lower else -lastPhysical.upper) = start)
    (finishEq : (if forward then lastPhysical.upper else -firstPhysical.lower) = finish) :
    if forward then BoundaryTraceParameters.firstParameter first.forward first.range = 0 ∧
      BoundaryTraceParameters.lastParameter last.forward last.range = 1
    else BoundaryTraceParameters.lastParameter last.forward last.range = 0 ∧ BoundaryTraceParameters.firstParameter
      first.forward first.range = 1 := by
  have firstInside : 0 ≤ BoundaryTraceParameters.firstParameter first.forward first.range ∧
    BoundaryTraceParameters.firstParameter first.forward first.range ≤ 1 := by
    cases first.forward with
    | true => exact ⟨first.within.1, first.range.ordered.le.trans first.within.2⟩
    | false => exact ⟨first.within.1.trans first.range.ordered.le, first.within.2⟩
  have lastInside : 0 ≤ BoundaryTraceParameters.lastParameter last.forward last.range ∧
    BoundaryTraceParameters.lastParameter last.forward last.range ≤ 1 := by
    cases last.forward with
    | true => exact ⟨last.within.1.trans last.range.ordered.le, last.within.2⟩
    | false => exact ⟨last.within.1, last.range.ordered.le.trans last.within.2⟩
  have left := BoundaryTraceParameters.parent_signed_bounds first.ordered firstInside
  have right := BoundaryTraceParameters.parent_signed_bounds last.ordered lastInside
  have leftOrdered := first.ordered
  have rightOrdered := last.ordered
  rw [firstForward] at left leftOrdered
  rw [lastForward] at right rightOrdered
  have firstRead := first.first_axis
  have lastRead := last.last_axis
  rw [firstForward] at firstRead ⊢
  rw [lastForward] at lastRead ⊢
  cases forward with
  | true =>
    have startRead := firstRead.trans startEq
    have finishRead := lastRead.trans finishEq
    exact ⟨parent_signed_parameter_eq leftOrdered (_root_.le_antisymm (startRead.trans_le firstBounds.1) left.1),
      BoundaryTraceParameters.parent_signed_parameter_eq rightOrdered (_root_.le_antisymm right.2 (lastBounds.2.trans_eq
        finishRead.symm))⟩
  | false =>
    have startRead := (congrArg Neg.neg lastRead).trans startEq
    have finishRead := (congrArg Neg.neg firstRead).trans finishEq
    exact ⟨parent_signed_parameter_eq rightOrdered (_root_.le_antisymm (startRead.trans_le lastBounds.1) right.1),
      BoundaryTraceParameters.parent_signed_parameter_eq leftOrdered (_root_.le_antisymm left.2 (firstBounds.2.trans_eq
        finishRead.symm))⟩

/-- Transport the endpoint readbacks to the actual bank positions without unfolding the executable chord acquisition in
an orientation case split. -/
theorem side_positions {comparison : prepared.ClosedBoundaryComparison other requested minimum}
    {vertical : Bool} {firstPhysical lastPhysical : PreparedAxisPartitions.Interval}
    (first : SourceChordData comparison vertical
      firstPhysical) (last : SourceChordData
      comparison vertical lastPhysical)
    (forward : Bool) {start finish : InverseRootPolynomial.Coordinate} {offset count : Nat}
    (endpoints : if forward then BoundaryTraceParameters.firstParameter first.forward first.range = 0 ∧
      BoundaryTraceParameters.lastParameter last.forward last.range = 1
      else BoundaryTraceParameters.lastParameter last.forward last.range = 0 ∧ BoundaryTraceParameters.firstParameter
        first.forward first.range = 1)
    (startEq : (if forward then firstPhysical.lower else -lastPhysical.upper) = start)
    (finishEq : (if forward then lastPhysical.upper else -firstPhysical.lower) = finish)
    (firstStart : SourceBlockParameters.signedAxis vertical forward ((comparison.Parent first.index).edge.point 0) =
      start → first.index.val = offset)
    (lastStart : SourceBlockParameters.signedAxis vertical forward ((comparison.Parent last.index).edge.point 0) = start
      → last.index.val = offset)
    (firstFinish : SourceBlockParameters.signedAxis vertical forward ((comparison.Parent first.index).edge.point 1) =
      finish → first.index.val + 1 = offset + count)
    (lastFinish : SourceBlockParameters.signedAxis vertical forward ((comparison.Parent last.index).edge.point 1) =
      finish → last.index.val + 1 = offset + count) :
    if forward then first.index.val = offset ∧ last.index.val + 1 = offset + count
    else last.index.val = offset ∧ first.index.val + 1 = offset + count := by
  have firstRead := first.first_axis
  have lastRead := last.last_axis
  cases forward with
  | true =>
    rw [endpoints.1] at firstRead
    rw [endpoints.2] at lastRead
    exact ⟨firstStart (firstRead.trans startEq), lastFinish (lastRead.trans finishEq)⟩
  | false =>
    rw [endpoints.2] at firstRead
    rw [endpoints.1] at lastRead
    exact ⟨lastStart ((congrArg Neg.neg lastRead).trans startEq),
      firstFinish ((congrArg Neg.neg firstRead).trans finishEq)⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordData

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram
namespace SurfacePreparation.ClosedBoundaryComparison

/-- The maximum original source density over every retained closed-bank parent position. -/
@[expose] def sourceMagnitude (comparison : prepared.ClosedBoundaryComparison other requested minimum) :
    InverseRootPolynomial.Coordinate :=
  PairedFragmentBlocks.maximum (comparison.sourceDensity)
    (List.ofFn (fun i : Fin comparison.original.plans.length => i))

end SurfacePreparation.ClosedBoundaryComparison
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram

open
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation.ClosedBoundaryComparison
  (sourceMagnitude)

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram
namespace SurfacePreparation.ClosedBoundaryComparison

/-- The maximum retained closed-bank source density is nonnegative. -/
theorem sourceMagnitude_nonnegative (comparison : prepared.ClosedBoundaryComparison other requested minimum) :
    0 ≤ comparison.sourceMagnitude :=
  PairedFragmentBlocks.maximum_nonnegative _ _

end SurfacePreparation.ClosedBoundaryComparison
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordData

/-- The cached original source chord is bounded by the common retained parent source magnitude. -/
theorem bounded {comparison : prepared.ClosedBoundaryComparison other requested minimum}
    {vertical : Bool} {physical : PreparedAxisPartitions.Interval}
    (chord : SourceChordData comparison vertical
      physical) : PrimitivePoint.Bounded chord.value comparison.sourceMagnitude := by
  have lower : 0 ≤ chord.range.lower ∧ chord.range.lower ≤ 1 :=
    ⟨chord.within.1, chord.range.ordered.le.trans chord.within.2⟩
  have upper : 0 ≤ chord.range.upper ∧ chord.range.upper ≤ 1 :=
    ⟨chord.within.1.trans chord.range.ordered.le, chord.within.2⟩
  have first : 0 ≤ BoundaryTraceParameters.firstParameter chord.forward chord.range ∧
      BoundaryTraceParameters.firstParameter chord.forward chord.range ≤ 1 := by
    cases chord.forward <;> assumption
  have last : 0 ≤ BoundaryTraceParameters.lastParameter chord.forward chord.range ∧
      BoundaryTraceParameters.lastParameter chord.forward chord.range ≤ 1 := by
    cases chord.forward <;> assumption
  have width : chord.range.upper - chord.range.lower ≤ 1 :=
    (Fraction.Order.Arithmetic.sub_le_sub_direct chord.within.2 chord.within.1).trans_eq (by ring1)
  have square : (BoundaryTraceParameters.lastParameter chord.forward chord.range -
    BoundaryTraceParameters.firstParameter chord.forward chord.range)^2 ≤ 1 := by
    have bound := Fraction.Order.Arithmetic.pow_le_pow_direct (Fraction.Order.Boundary.sub_nonnegative_iff.mpr
      chord.range.ordered.le) width 2
    have eq : (BoundaryTraceParameters.lastParameter chord.forward chord.range - BoundaryTraceParameters.firstParameter
      chord.forward chord.range)^2 =
        (chord.range.upper - chord.range.lower)^2 := by
      cases chord.forward
      · dsimp [BoundaryTraceParameters.lastParameter, BoundaryTraceParameters.firstParameter]
        ring1
      · rfl
    exact eq.trans_le (bound.trans_eq (by ring1))
  have density : comparison.sourceDensity chord.index ≤ comparison.sourceMagnitude :=
    PairedFragmentBlocks.le_maximum _ (Data.List.OfFn.Basic.mem_ofFn.mpr ⟨chord.index, rfl⟩)
  have left := (comparison.entries.get chord.index).source.increment_bound first last
  have right := (comparison.entries.get chord.index).otherSource.increment_bound first last
  have factor := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct square
    (comparison.sourceDensity_nonnegative chord.index)).trans_eq
    (mul_one (comparison.sourceDensity chord.index))
  rw [chord.value_eq]
  have leftBound := left.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Basic.le_max_left _ _) (Fraction.Order.Arithmetic.sq_nonneg_direct _)).trans (factor.trans density))
  have rightBound := right.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Basic.le_max_right _ _) (Fraction.Order.Arithmetic.sq_nonneg_direct _)).trans (factor.trans
    density))
  constructor
  · change Fraction.Order.Basic.LessEqual _ _ at leftBound ⊢
    simp only [Data.Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] at leftBound
    convert leftBound using 1
    rfl
  · change Fraction.Order.Basic.LessEqual _ _ at rightBound ⊢
    simp only [Data.Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] at rightBound
    convert rightBound using 1
    rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordData

end
