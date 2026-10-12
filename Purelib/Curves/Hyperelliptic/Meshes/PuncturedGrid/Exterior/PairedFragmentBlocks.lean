module
import Purelib.Algebra.FiniteSum.Rational.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Integration.RectangularPairedPointBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularPairedSegments
import Purelib.Riemann.Paths.RectangularSegmentRefinement
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments
public import Purelib.Integration.Path.CenteredPathIncrements
import Purelib.Integration.Path.PairedBlockComparison
public import Purelib.Geometry.Rectangle.SourceIntervals
public import Purelib.Riemann.Paths.RectangularTraceParameterReadings
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Tactic.Ring

public section

open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann
open Purelib

/-! Compose retained owner-aware fragments without discarding the polygon
of fragment totals. All analytic bounds come from the actual source entries. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea

open Purelib.Riemann.Normalization
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)

open Purelib.Data.Rat.Fraction.Compatibility
variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential} {target : Normalization.InverseRootPolynomial.Coordinate} {minimum stage fine index :
    Nat}
  {box otherBox : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {plan : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan occurrence other target
    minimum}

set_option genInjectivity false in
/-- Geometry and cached readings of one retained fragment. No analytic
area or total estimate is requested from the caller. Counts may differ. -/
structure OwnedFragment (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine)
    (data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.FirstData occurrence index) (otherData :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.SecondData occurrence other index) where
  /-- The original paired source entry used by this fragment. -/ entry :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry plan sample otherSample fine
  /-- The retained source entry belongs to the exact supplied parent evaluation. -/ member : entry ∈ evaluated.retained
  /-- The retained common geometric fragment of that original parent. -/ piece :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.Fragment entry
  /-- The number of actual sampled increments. -/ count : Nat
  /-- All original sample parameters, including repeated values. -/ parameters : Fin (count + 1) →
    Normalization.InverseRootPolynomial.Coordinate
  /-- Every retained parameter lies in the original fragment interval. -/ inside : ∀ vertex, piece.interval.lower ≤
    parameters vertex ∧ parameters vertex ≤ piece.interval.upper
  /-- The retained traversal orientation of the source parameters. -/ forward : Bool
  /-- Consecutive original parameters follow the retained traversal orientation. -/ ordered : ∀ edge : Fin count, if
    forward then parameters edge.castSucc ≤ parameters edge.succ
    else parameters edge.succ ≤ parameters edge.castSucc
  /-- The retained length-error allocation. -/ allowance : Normalization.InverseRootPolynomial.Coordinate
  /-- The original finite length-error budget for this actual increment count. -/ budget :
    Path.NoisyPathArea.LengthErrorBudget count allowance
  /-- Both original point-owner requests at the retained budget tolerance. -/ owners :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest.OwnerRequest occurrence other budget.tolerance
  /-- The shared face stage pays both retained owner requests. -/ later : owners.index ≤ index
  /-- The actual first-differential point-owner readings at the retained parameters. -/ first :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments.FirstReadings entry data parameters
  /-- The actual recast second-differential readings at those same parameters. -/ second :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments.SecondReadings entry otherData parameters
  /-- The cached sample of the original paired point-owner values. -/ owned : Periods.CenteredBilinearPath.Sample
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments.ownedValues first second)
  /-- The cached sample of the original paired source primitive values. -/ source : Periods.CenteredBilinearPath.Sample
    (fun vertex => Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceValues entry (parameters
    vertex))

constructive_injectivity OwnedFragment

set_option genInjectivity false in
/-- A shared positive cap for the owner and trace-error terms of the
fragment area rate. The density bound is fixed before either cap is used. -/
structure FragmentAreaBudget (density target : Normalization.InverseRootPolynomial.Coordinate) where
  /-- The fixed complete trace-density bound is nonnegative. -/ density_nonnegative : 0 ≤ density
  /-- The cached common local owner and trace-error allowance. -/ tolerance :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The cached allowance is the weighted allocation for the full scalar area-rate coefficient. -/ tolerance_eq :
    tolerance = Rational.Budget.Weighted.allowance target (320 * (4 * density + 3) + 80 * density)
  /-- The retained local allowance is strictly positive. -/ tolerance_positive : 0 < tolerance
  /-- The displayed owner and trace-error contributions fit the requested area target. -/ paid : 320 * tolerance * (4 *
    density + 3) + 80 * tolerance * density ≤ target

constructive_injectivity FragmentAreaBudget

/-- Allocate one positive tolerance paying both owner and trace-error contributions at the fixed nonnegative density. -/
@[expose] def FragmentAreaBudget.build (density target : Normalization.InverseRootPolynomial.Coordinate) (nonnegative :
  0 ≤ density) (positive : 0 < target) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.FragmentAreaBudget density target := by
  let weight := 320 * (4 * density + 3) + 80 * density
  have weightNonnegative : 0 ≤ weight := add_nonneg
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by
        decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 320)
      (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) nonnegative) (by decide)))
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by
        decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 80) nonnegative)
  let tolerance := Rational.Budget.Weighted.allowance target weight
  refine ⟨nonnegative, tolerance, rfl, Rational.Budget.Weighted.allowance_positive positive weightNonnegative, ?_⟩
  have paid := Rational.Budget.Weighted.mul_allowance_le positive.le weightNonnegative
  exact (show 320 * tolerance * (4 * density + 3) + 80 * tolerance * density = weight * tolerance by
      dsimp [weight];
      ring1).trans_le paid

/-- The retained common tolerance pays the displayed area rate whenever the original owner error, query error and
density meet their bounds. -/
theorem FragmentAreaBudget.bound {density target t d e : Normalization.InverseRootPolynomial.Coordinate} (budget :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.FragmentAreaBudget density target)
    (hd : 0 ≤ d)
    (ownerLe : t ≤ budget.tolerance) (densityLe : d ≤ density) (errorLe : e ≤ budget.tolerance) :
    320 * t * (4 * d + 3) + 80 * e * d ≤ target := by
  have first := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct ownerLe (by
        decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 320))
    (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by
        decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 4) hd) (by
          decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 3))).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          densityLe (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 4)) le_rfl)
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by
            decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 320) budget.tolerance_positive.le))
  have second := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct errorLe (by
        decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 80)) hd).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct densityLe (Fraction.Order.Arithmetic.mul_nonneg_direct
        (by decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 80) budget.tolerance_positive.le))
  exact (Fraction.Order.Arithmetic.add_le_add_direct first second).trans budget.paid

/-- Four times the retained local tolerance fits the complete area target. -/
theorem FragmentAreaBudget.four_tolerance_le {density target : Normalization.InverseRootPolynomial.Coordinate} (budget :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.FragmentAreaBudget density target) :
    4 * budget.tolerance ≤ target := by
  have factor : (1 : Normalization.InverseRootPolynomial.Coordinate) ≤ 4 * density + 3 :=
    (by decide : (1 : Normalization.InverseRootPolynomial.Coordinate) ≤ 3).trans
      (le_add_of_nonneg_left (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) budget.density_nonnegative))
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct factor
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by
        decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 320) budget.tolerance_positive.le)
  rw [mul_one] at scaled
  have first := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by
      decide +kernel : (4 : Normalization.InverseRootPolynomial.Coordinate) ≤ 320)
    budget.tolerance_positive.le).trans scaled
  exact (first.trans (le_add_of_nonneg_right
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by
        decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 80) budget.tolerance_positive.le)
      budget.density_nonnegative))).trans budget.paid

namespace OwnedFragment
variable {evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine}
  {data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.FirstData occurrence index} {otherData :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.SecondData occurrence other index}

/-- Consume the physical trace's retained owners, values and area sample at
the certified parent parameters. The location may come from a different
shared mesh geometry; neither primitive bank is evaluated by this adapter. -/
@[expose] def ofTrace (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry plan sample
  otherSample fine) (member : entry ∈ evaluated.retained)
    {cuts : Paths.RectangularSegmentSplitting.GridCuts occurrence.compared.entered.domain.geometry}
    {split : Paths.RectangularSegmentSplitting.SegmentSplit cuts (entry.plan.parent.edge.point 0)
      (entry.plan.parent.edge.point 1)}
    {interval : Rectangle.Partition.PreparedAxisPartitions.Interval} (located :
      Paths.RectangularSegmentRefinement.Subinterval split interval)
    {leftColumns leftRows rightColumns rightRows count : Nat}
    {leftGeometry : Normalization.RectangularInverseModels.Geometry leftColumns leftRows}
    {rightGeometry : Normalization.RectangularInverseModels.Geometry rightColumns rightRows}
    {physical : Paths.RectangularPairedSegments.PairedSegmentPiece leftGeometry rightGeometry}
    {trace : Integration.RectangularPairedPointBanks.Trace physical count}
    (forward : Bool)
    (transport : Paths.RectangularTraceParameterReadings.ParentParameters trace entry.plan.parent
      (if forward then interval.lower else interval.upper) (if forward then interval.upper else interval.lower))
    (increasing : ∀ edge : Fin count, trace.parameters edge.castSucc ≤ trace.parameters edge.succ)
    {allowance : Normalization.InverseRootPolynomial.Coordinate} (budget : Path.NoisyPathArea.LengthErrorBudget count
      allowance)
    (owners : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest.OwnerRequest occurrence other
      budget.tolerance) (later : owners.index ≤ index)
    (first : Readings.RectangularPointReadings.PointReadings data.anchors data.offsets (fun vertex => trace.points
      vertex))
    (second : Readings.RectangularPointReadings.PointReadings otherData.anchors otherData.offsets (fun vertex =>
      trace.points vertex))
    (owned : Periods.CenteredBilinearPath.Sample (fun vertex => (⟨first.values vertex, second.values vertex⟩ :
      Topology.Polygon.Stokes.PrimitivePoint)))
    (source : Periods.CenteredBilinearPath.Sample (fun vertex =>
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceValues entry (transport.parameters
      vertex))) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment evaluated data otherData :=
  { entry := entry, member := member, piece := located.piece, count := count
    parameters := transport.parameters
    inside := by
      intro vertex
      apply located.contains
      cases forward with
      | true => exact transport.inside interval.ordered.le vertex
      | false => exact transport.inside_reverse interval.ordered.le vertex
    forward := forward
    ordered := by
      cases forward with
      | true => exact transport.ordered interval.ordered.le increasing
      | false => exact transport.ordered_reverse interval.ordered.le increasing
    allowance := allowance, budget := budget, owners := owners, later := later
    first := transport.readings first, second := transport.readings second
    owned := owned, source := source }

/-- Select the containing source fragment from the physical shared mesh.
The supplied point readings and both area samples are reused unchanged. -/
@[expose] def ofMesh (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry plan sample
  otherSample fine) (member : entry ∈ evaluated.retained)
    {cuts : Paths.RectangularSegmentSplitting.GridCuts occurrence.compared.entered.domain.geometry}
    (split : Paths.RectangularSegmentSplitting.SegmentSplit cuts (entry.plan.parent.edge.point 0)
      (entry.plan.parent.edge.point 1))
    {meshBox : Rational.Box} (mesh : Meshes.RectangularObservationMesh.ObservationMesh cuts meshBox)
    (retained : ∀ point ∈ split.points, point ∈ mesh.points)
    (vertical : Bool) (physical : Rectangle.Partition.PreparedAxisPartitions.Interval) (present : physical ∈
      Rectangle.SourceIntervals.axisIntervals mesh vertical)
    (interval : Rectangle.Partition.PreparedAxisPartitions.Interval) (within : 0 ≤ interval.lower ∧ interval.upper ≤ 1)
    (correspondence : Rectangle.SourceIntervals.AxisCorrespondence vertical
      (entry.plan.parent.edge.point 0) (entry.plan.parent.edge.point 1) interval physical)
    {count : Nat} (parameters : Fin (count + 1) → Normalization.InverseRootPolynomial.Coordinate)
    (inside : ∀ vertex, interval.lower ≤ parameters vertex ∧ parameters vertex ≤ interval.upper)
    (ordered : ∀ edge : Fin count, parameters edge.castSucc ≤ parameters edge.succ)
    {allowance : Normalization.InverseRootPolynomial.Coordinate} (budget : Path.NoisyPathArea.LengthErrorBudget count
      allowance)
    (owners : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest.OwnerRequest occurrence other
      budget.tolerance) (later : owners.index ≤ index)
    (first : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments.FirstReadings entry data parameters)
      (second : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments.SecondReadings entry otherData
      parameters)
    (owned : Periods.CenteredBilinearPath.Sample
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments.ownedValues first second))
    (source : Periods.CenteredBilinearPath.Sample (fun vertex =>
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceValues entry (parameters vertex))) :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment evaluated data otherData :=
  let located := Rectangle.SourceIntervals.locateSourceInterval mesh split retained vertical physical present interval
    within correspondence
  { entry := entry, member := member, piece := located.piece, count := count, parameters := parameters
    inside := fun vertex => located.contains (inside vertex)
    forward := true, ordered := ordered, allowance := allowance, budget := budget, owners := owners, later := later
    first := first, second := second, owned := owned, source := source }

/-- A junction may have two different owners at the same parameter. Keep
both cached readings and the intervening increment; no owner equality is used. -/
@[expose] def atJunction (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry plan
  sample otherSample fine) (member : entry ∈ evaluated.retained)
    {cuts : Paths.RectangularSegmentSplitting.GridCuts occurrence.compared.entered.domain.geometry}
    (split : Paths.RectangularSegmentSplitting.SegmentSplit cuts (entry.plan.parent.edge.point 0)
      (entry.plan.parent.edge.point 1))
    (parameter : Normalization.InverseRootPolynomial.Coordinate) (inside : 0 ≤ parameter ∧ parameter ≤ 1)
    {allowance : Normalization.InverseRootPolynomial.Coordinate} (budget : Path.NoisyPathArea.LengthErrorBudget 1
      allowance)
    (owners : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest.OwnerRequest occurrence other
      budget.tolerance) (later : owners.index ≤ index)
    (first : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments.FirstReadings entry data (fun _ : Fin 2 =>
      parameter))
    (second : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments.SecondReadings entry otherData (fun _ :
      Fin 2 => parameter))
    (owned : Periods.CenteredBilinearPath.Sample
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments.ownedValues first second))
    (source : Periods.CenteredBilinearPath.Sample (fun _ : Fin 2 =>
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceValues entry parameter)) :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment evaluated data otherData :=
  let located := split.locate parameter inside
  { entry := entry, member := member, piece := located.piece, count := 1, parameters := fun _ => parameter
    inside := fun _ => located.inside, forward := true, ordered := fun _ => le_rfl
    allowance := allowance, budget := budget, owners := owners, later := later
    first := first, second := second, owned := owned, source := source }

/-- Read the two increment lists already retained by the owned and source samples. -/
@[expose] def pair (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment evaluated
  data otherData) : List Topology.Polygon.Stokes.PrimitivePoint × List PrimitivePoint :=
  ((Path.CenteredPathIncrements.Sample.increments fragment.owned), (Path.CenteredPathIncrements.Sample.increments
    fragment.source))

/-- The original fragment's total parameter displacement in its retained orientation. -/
@[expose] def width (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment evaluated
  data otherData) : Coordinate :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep fragment.forward (fragment.parameters 0)
    (fragment.parameters (Fin.last fragment.count))

/-- The retained ordered parameter width is nonnegative. -/
theorem width_nonnegative (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment
  evaluated data otherData) : 0 ≤ fragment.width := open Purelib.Algebra in by
  have bound := Algebra.FiniteSum.Rational.Order.weight_sum_nonnegative
    (fun edge : Fin fragment.count => Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep
      fragment.forward (fragment.parameters edge.castSucc) (fragment.parameters edge.succ))
    (fun edge => Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep_nonnegative
      fragment.forward _ _ (fragment.ordered edge))
  exact bound.trans_eq (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterSteps_total
    fragment.forward fragment.parameters)

/-- The retained unit-interval parameter width is at most one. -/
theorem width_le_one (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment
  evaluated data otherData) : fragment.width ≤ 1 := by
  have zeroDifference (value : Purelib.Data.Rat.Fraction.Rational) : value - 0 = value := by ring1
  have unit (vertex : Fin (fragment.count + 1)) : 0 ≤ fragment.parameters vertex ∧ fragment.parameters vertex ≤ 1 :=
    ⟨fragment.piece.within.1.trans (fragment.inside vertex).1, (fragment.inside vertex).2.trans fragment.piece.within.2⟩
  cases direction : fragment.forward with
  | true =>
    have bound := Fraction.Order.Arithmetic.sub_le_sub_direct (unit (Fin.last fragment.count)).2 (unit 0).1
    rw [zeroDifference] at bound
    change Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep fragment.forward
      (fragment.parameters 0) (fragment.parameters (Fin.last fragment.count)) ≤ 1
    rw [direction]
    exact bound
  | false =>
    have bound := Fraction.Order.Arithmetic.sub_le_sub_direct (unit 0).2 (unit (Fin.last fragment.count)).1
    rw [zeroDifference] at bound
    change Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep fragment.forward
      (fragment.parameters 0) (fragment.parameters (Fin.last fragment.count)) ≤ 1
    rw [direction]
    exact bound

/-- The complete computed owner and grid-to-source area-error bound for this retained fragment. -/
@[expose] def areaError (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment
  evaluated data otherData) : Coordinate :=
  2 * (40 * fragment.budget.tolerance * (4 * Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.traceDensity
    fragment.entry fragment.piece index + 3) *
    (fragment.width + fragment.allowance) ^ 2 +
    40 * Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.traceError fragment.entry fragment.piece index *
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.traceDensity fragment.entry fragment.piece index *
      fragment.width ^ 2)

/-- The retained fragment's complete paired trace density is nonnegative. -/
theorem density_nonnegative (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment
  evaluated data otherData) :
    0 ≤ Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.traceDensity fragment.entry fragment.piece index
      :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.queryDensity_nonnegative ..)
      (Gaussian.Norm.Basic.normSq_nonneg _))
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.sourceDensity_nonnegative _))

/-- Unit width and bounded padding reduce the full scalar fragment-area expression to its displayed linear error rate.
-/
private theorem area_rate_scalar {t d e w a : Normalization.InverseRootPolynomial.Coordinate}
    (ht : 0 ≤ t) (hd : 0 ≤ d) (he : 0 ≤ e) (hw : w ^ 2 ≤ 1) (ha : (w + a) ^ 2 ≤ 4) :
    2 * (40 * t * (4 * d + 3) * (w + a) ^ 2 + 40 * e * d * w ^ 2) ≤
      320 * t * (4 * d + 3) + 80 * e * d := by
  have first := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct ha
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by
        decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 40) ht)
      (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by
          decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 4) hd) (by
            decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 3)))
  have second := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct hw
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by
        decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 40) he) hd)
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct first
    second) (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)).trans_eq (by ring1)

/-- Eliminate the sampled parameter width from the error rate using its
retained unit-interval containment, in either source orientation. -/
theorem areaError_rate (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment
  evaluated data otherData) (allowanceLe : fragment.allowance ≤ 1) :
    fragment.areaError ≤ 320 * fragment.budget.tolerance * (4 *
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.traceDensity fragment.entry fragment.piece index +
      3) +
      80 * Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.traceError fragment.entry fragment.piece index
        * Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.traceDensity fragment.entry fragment.piece
        index := by
  have densityNonnegative := fragment.density_nonnegative
  have errorNonnegative : 0 ≤ Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.traceError fragment.entry
    fragment.piece index :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.queryDensity_nonnegative ..)
      (occurrence.compared.entered.domain.geometry.box fragment.piece.column fragment.piece.row).diagonalSq_nonneg
  have allowanceNonnegative : 0 ≤ fragment.allowance :=
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le fragment.count))
      fragment.budget.padding_positive.le).trans fragment.budget.paid
  have widthSquare : fragment.width ^ 2 ≤ 1 :=
    (Fraction.Order.Arithmetic.pow_le_pow_direct fragment.width_nonnegative fragment.width_le_one 2).trans_eq (by
      decide)
  have paddedSquare : (fragment.width + fragment.allowance) ^ 2 ≤ 4 :=
    (Fraction.Order.Arithmetic.pow_le_pow_direct (add_nonneg fragment.width_nonnegative allowanceNonnegative)
      (Fraction.Order.Arithmetic.add_le_add_direct fragment.width_le_one allowanceLe) 2).trans_eq (by decide)
  exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment.area_rate_scalar
    fragment.budget.tolerance_positive.le densityNonnegative errorNonnegative widthSquare paddedSquare

/-- The retained area budget pays the complete fragment error when its actual density and two local errors meet the
allocated bounds. -/
theorem areaError_paid (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment
  evaluated data otherData) {density target : Normalization.InverseRootPolynomial.Coordinate}
    (budget : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.FragmentAreaBudget density target)
      (allowanceLe : fragment.allowance ≤ 1)
    (densityLe : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.traceDensity fragment.entry
      fragment.piece index ≤ density)
    (ownerLe : fragment.budget.tolerance ≤ budget.tolerance)
    (errorLe : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.traceError fragment.entry fragment.piece
      index ≤ budget.tolerance) : fragment.areaError ≤ target :=
  (fragment.areaError_rate allowanceLe).trans (budget.bound fragment.density_nonnegative ownerLe densityLe errorLe)

/-- The computed paired endpoint-total discrepancy from actual owner tolerance and source-query displacement. -/
@[expose] def totalError (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment
  evaluated data otherData) : Coordinate :=
  2 * (fragment.budget.tolerance + Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.queryDensity
    fragment.entry fragment.piece index * Data.Gaussian.Norm.Basic.normSq
    (fragment.entry.plan.parent.edge.point (fragment.parameters (Fin.last fragment.count)) -
      fragment.entry.plan.parent.edge.point (fragment.parameters 0)))

/-- The original source-total magnitude bound from retained slope and squared parameter width. -/
@[expose] def sourceBound (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment
  evaluated data otherData) : Coordinate :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceDensity fragment.entry * fragment.width ^ 2

/-- A paid retained query tail bounds the original endpoint-total discrepancy at every later face stage. -/
theorem totalError_tail (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment
  evaluated data otherData) {radius : Normalization.InverseRootPolynomial.Coordinate}
    (tail : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.PairedQueryTail fragment.entry
      fragment.piece radius) (later : tail.index ≤ index) :
    fragment.totalError ≤ 2 * (fragment.budget.tolerance + tail.ceiling * Data.Gaussian.Norm.Basic.normSq
      (fragment.entry.plan.parent.edge.point (fragment.parameters (Fin.last fragment.count)) -
        fragment.entry.plan.parent.edge.point (fragment.parameters 0))) :=
  Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct le_rfl (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (tail.accurate index later) (Gaussian.Norm.Basic.normSq_nonneg _)))
    (by decide)

/-- The common computed magnitude bound for both original owned and source totals. -/
@[expose] def totalBound (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment
  evaluated data otherData) : Coordinate :=
  2 * (fragment.totalError + fragment.sourceBound)

/-- The actual endpoint discrepancy is bounded by owner tolerance and the original fragment cell's trace error. -/
theorem totalError_rate (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment
  evaluated data otherData) :
    fragment.totalError ≤ 2 * (fragment.budget.tolerance +
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.traceError fragment.entry fragment.piece index) :=
      by
  have displacement := Rational.Box.normSq_sub_le_diagonalSq
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.fragment_contains fragment.entry fragment.piece _
      (fragment.inside (Fin.last fragment.count)))
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.fragment_contains fragment.entry fragment.piece _
      (fragment.inside 0))
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct le_rfl (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      displacement (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.queryDensity_nonnegative ..))) (by
      decide)

/-- The retained area budget also pays the complete endpoint-total discrepancy under its two local error bounds. -/
theorem totalError_paid (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment
  evaluated data otherData) {density target : Normalization.InverseRootPolynomial.Coordinate}
    (budget : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.FragmentAreaBudget density target)
      (ownerLe : fragment.budget.tolerance ≤ budget.tolerance)
    (errorLe : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.traceError fragment.entry fragment.piece
      index ≤ budget.tolerance) : fragment.totalError ≤ target := by
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
    ownerLe errorLe) (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
  have bounded : fragment.totalError ≤ 4 * budget.tolerance :=
    (fragment.totalError_rate.trans scaled).trans_eq (by ring1)
  exact bounded.trans budget.four_tolerance_le

/-- The original unit-interval source-total bound is at most the retained source density. -/
theorem sourceBound_uniform (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment
  evaluated data otherData) :
    fragment.sourceBound ≤ Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceDensity fragment.entry
      := by
  have widthSquare : fragment.width ^ 2 ≤ 1 :=
    (Fraction.Order.Arithmetic.pow_le_pow_direct fragment.width_nonnegative fragment.width_le_one 2).trans_eq (by
      decide)
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct widthSquare
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.sourceDensity_nonnegative fragment.entry)).trans_eq
    (mul_one _)

/-- A paid endpoint discrepancy gives the displayed common total bound using the original source density. -/
theorem totalBound_uniform (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment
  evaluated data otherData) {target : Normalization.InverseRootPolynomial.Coordinate}
    (errorLe : fragment.totalError ≤ target) : fragment.totalBound ≤ 2 * (target +
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceDensity fragment.entry) :=
  Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct errorLe
    fragment.sourceBound_uniform) (by decide)

/-- The actual retained owned and source increment areas differ by at most the computed area error. -/
theorem area_accurate (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment
  evaluated data otherData) :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area fragment.pair.1 - Path.PairedIncrementArea.area
      fragment.pair.2) ≤ fragment.areaError := by
  change Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area
    (Path.CenteredPathIncrements.Sample.increments fragment.owned) -
    Path.PairedIncrementArea.area (Path.CenteredPathIncrements.Sample.increments fragment.source)) ≤ _
  rw [Path.CenteredPathIncrements.Sample.increments_area fragment.owned,
    Path.CenteredPathIncrements.Sample.increments_area fragment.source]
  exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments.owned_fragment_area_bound evaluated
    fragment.entry fragment.member fragment.piece data otherData
    fragment.parameters fragment.inside fragment.forward fragment.ordered fragment.budget fragment.owners fragment.later
    fragment.first fragment.second fragment.owned fragment.source

/-- Both actual retained endpoint totals differ by at most the computed paired total error. -/
theorem total_accurate (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment
  evaluated data otherData) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      ((Path.PairedIncrementArea.total fragment.pair.1).sub
        (Path.PairedIncrementArea.total fragment.pair.2)) fragment.totalError := by
  change Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
    ((Path.PairedIncrementArea.total (Path.CenteredPathIncrements.Sample.increments fragment.owned)).sub
      (Path.PairedIncrementArea.total (Path.CenteredPathIncrements.Sample.increments fragment.source))) _
  rw [Path.CenteredPathIncrements.Sample.increments_total fragment.owned,
    Path.CenteredPathIncrements.Sample.increments_total fragment.source]
  exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments.owned_fragment_increment_error evaluated
    fragment.entry fragment.member fragment.piece data otherData
    fragment.parameters fragment.inside fragment.owners fragment.later fragment.first fragment.second 0 (Fin.last
      fragment.count)

/-- Both retained source-path totals meet the original source bound. -/
theorem source_bounded (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment
  evaluated data otherData) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      (Path.PairedIncrementArea.total fragment.pair.2) fragment.sourceBound := by
  change Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
    (Path.PairedIncrementArea.total (Path.CenteredPathIncrements.Sample.increments fragment.source)) _
  rw [Path.CenteredPathIncrements.Sample.increments_total fragment.source]
  unfold Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment.sourceBound
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment.width
  rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep_sq]
  exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.source_increment_bound fragment.entry
    fragment.piece _ _ (fragment.inside 0) (fragment.inside (Fin.last fragment.count))

/-- The computed original endpoint-total error is nonnegative. -/
theorem totalError_nonnegative (fragment :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment evaluated data otherData) : 0 ≤
  fragment.totalError :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg fragment.budget.tolerance_positive.le
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.queryDensity_nonnegative ..)
      (Gaussian.Norm.Basic.normSq_nonneg _)))

/-- The computed original source-total magnitude bound is nonnegative. -/
theorem sourceBound_nonnegative (fragment :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment evaluated data otherData) : 0 ≤
  fragment.sourceBound :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.sourceDensity_nonnegative _)
    (Fraction.Order.Arithmetic.sq_nonneg_direct _)

/-- The computed common total bound is nonnegative. -/
theorem totalBound_nonnegative (fragment :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment evaluated data otherData) : 0 ≤
  fragment.totalBound :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg fragment.totalError_nonnegative
    fragment.sourceBound_nonnegative)

/-- Both actual retained owned-path totals meet the computed common total bound. -/
theorem owned_bounded (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment
  evaluated data otherData) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      (Path.PairedIncrementArea.total fragment.pair.1) fragment.totalBound := by
  have scalar {a b : Normalization.InverseRootPolynomial.Gaussian} (error : Data.Gaussian.Norm.Basic.normSq (a - b)
    ≤ fragment.totalError)
      (source : Data.Gaussian.Norm.Basic.normSq b ≤ fragment.sourceBound) : Data.Gaussian.Norm.Basic.normSq a ≤
        fragment.totalBound := by
    have estimate := Gaussian.Norm.Bounds.normSq_add_le_two (a - b) b
    rw [sub_add_cancel] at estimate
    exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct error source) (by decide))
  have oldBound {value : Gaussian.Basic.Canonical} {limit : Normalization.InverseRootPolynomial.Coordinate}
      (bound : Gaussian.Basic.Canonical.normSq value ≤ limit) :
      Data.Gaussian.Norm.Basic.normSq value ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at bound ⊢
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] using bound
  have canonicalBound {value : Gaussian.Basic.Canonical} {limit : Normalization.InverseRootPolynomial.Coordinate}
      (bound : Data.Gaussian.Norm.Basic.normSq value ≤ limit) :
      Gaussian.Basic.Canonical.normSq value ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at bound ⊢
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] using bound
  exact ⟨canonicalBound (scalar (oldBound fragment.total_accurate.1) (oldBound fragment.source_bounded.1)),
    canonicalBound (scalar (oldBound fragment.total_accurate.2) (oldBound fragment.source_bounded.2))⟩

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment in
/-- Both retained source-path totals also meet the same computed common total bound. -/
theorem source_bounded_total (fragment : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment
  evaluated data otherData) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      (Path.PairedIncrementArea.total fragment.pair.2) fragment.totalBound := by
  have upper : fragment.sourceBound ≤ fragment.totalBound :=
    (le_add_of_nonneg_right (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by
        decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
      fragment.totalError_nonnegative) fragment.sourceBound_nonnegative)).trans_eq (by unfold totalBound; ring1)
  exact ⟨fragment.source_bounded.1.trans upper, fragment.source_bounded.2.trans upper⟩

end OwnedFragment

/-- Compute the finite maximum of supplied rational values with zero as the empty-list value. -/
@[expose] def maximum {Item : Type u} (value : Item → Normalization.InverseRootPolynomial.Coordinate) : List Item →
  Normalization.InverseRootPolynomial.Coordinate
  | [] => 0
  | item :: rest => max (value item)
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum value rest)

/-- The zero-based finite maximum is nonnegative. -/
theorem maximum_nonnegative {Item : Type u} (value : Item → Normalization.InverseRootPolynomial.Coordinate) (items :
  List Item) :
    0 ≤ Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum value items := by
  induction items with
  | nil => exact le_rfl
  | cons item rest ih => exact ih.trans (Fraction.Order.Basic.le_max_right ..)

/-- Every original list entry's value is bounded by the computed maximum. -/
theorem le_maximum {Item : Type u} (value : Item → Normalization.InverseRootPolynomial.Coordinate) {items : List Item}
  {item : Item}
    (member : item ∈ items) : value item ≤ Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum
      value items := by
  induction items with
  | nil => cases member
  | cons first rest ih =>
    rcases Data.List.Membership.mem_cons.mp member with rfl | member
    · exact Fraction.Order.Basic.le_max_left ..
    · exact (ih member).trans (Fraction.Order.Basic.le_max_right ..)

/-- A nonnegative bound on every original list entry also bounds the computed maximum.

The zero-based maximum follows the retained list spine. Its head value and the
maximum of its original tail remain below the same supplied scalar ceiling. -/
theorem maximum_le {Item : Type u} (value : Item → Normalization.InverseRootPolynomial.Coordinate) (items : List Item)
    {bound : Normalization.InverseRootPolynomial.Coordinate} (nonnegative : 0 ≤ bound) (bounded : ∀ item ∈ items, value
      item ≤ bound) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum value items ≤ bound := by
  induction items with
  | nil => exact nonnegative
  | cons first rest ih =>
    exact Fraction.Order.Basic.max_le (bounded first List.mem_cons_self)
      (ih (fun item member => bounded item (List.mem_cons_of_mem _ member)))

/-- Executable full-path error bound, independent of the sum of fine vertex
counts except through the retained local owner budgets. -/
@[expose] def fragmentBlockError {evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine}
    {data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.FirstData occurrence index} {otherData :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.SecondData occurrence other index}
    (fragments : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment evaluated data
      otherData)) : Coordinate :=
  2 * ((fragments.length : Normalization.InverseRootPolynomial.Coordinate) ^ 2 *
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment.areaError fragments +
    16 * (fragments.length : Normalization.InverseRootPolynomial.Coordinate) ^ 4 *
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment.totalError fragments *
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment.totalBound fragments)

/-- Allocate the local tolerance paying both internal areas and the full cross-fragment polygon at the actual fragment
count. -/
@[expose] def fragmentLocalTolerance (count : Nat) (totalBound target : Normalization.InverseRootPolynomial.Coordinate)
  : Coordinate :=
  target / (2 * ((count : Normalization.InverseRootPolynomial.Coordinate) ^ 2 + 16 * (count :
    Normalization.InverseRootPolynomial.Coordinate) ^ 4 * totalBound) + 1)

/-- The complete count-dependent fragment comparison coefficient is nonnegative for a nonnegative total bound. -/
private theorem fragmentCoefficient_nonnegative (count : Nat) {bound : Normalization.InverseRootPolynomial.Coordinate}
  (nonnegative : 0 ≤ bound) :
    0 ≤ 2 * ((count : Normalization.InverseRootPolynomial.Coordinate) ^ 2 + 16 * (count :
      Normalization.InverseRootPolynomial.Coordinate) ^ 4 * bound) :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg (Fraction.Order.Arithmetic.sq_nonneg_direct _)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)) 4))
      nonnegative))

/-- A positive global target and nonnegative total bound give a strictly positive local fragment tolerance. -/
theorem fragmentLocalTolerance_positive (count : Nat) {bound target : Normalization.InverseRootPolynomial.Coordinate}
    (nonnegative : 0 ≤ bound) (positive : 0 < target) : 0 <
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.fragmentLocalTolerance count bound target :=
  Fraction.Order.Field.div_pos_direct positive (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.fragmentCoefficient_nonnegative count nonnegative)
    (by decide))

/-- Pays the complete cross-fragment polygon using the actual fragment count.
The local obligations concern the existing computed errors, not new samples. -/
theorem fragmentBlockError_lt {evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine}
    {data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.FirstData occurrence index} {otherData :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.SecondData occurrence other index}
    (fragments : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment evaluated data
      otherData)) {bound target : Normalization.InverseRootPolynomial.Coordinate}
    (nonnegative : 0 ≤ bound) (positive : 0 < target)
    (areas : ∀ fragment ∈ fragments, fragment.areaError ≤
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.fragmentLocalTolerance fragments.length bound
      target)
    (errors : ∀ fragment ∈ fragments, fragment.totalError ≤
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.fragmentLocalTolerance fragments.length bound
      target)
    (totals : ∀ fragment ∈ fragments, fragment.totalBound ≤ bound) :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.fragmentBlockError fragments < target := by
  let tolerance := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.fragmentLocalTolerance
    fragments.length bound target
  have tolerancePositive : 0 < tolerance :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.fragmentLocalTolerance_positive _ nonnegative
    positive
  have areaMax := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum_le
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment.areaError fragments
    tolerancePositive.le areas
  have errorMax := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum_le
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment.totalError fragments
    tolerancePositive.le errors
  have totalMax := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum_le
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment.totalBound fragments nonnegative
    totals
  have fourth : 0 ≤ 16 * (fragments.length : Normalization.InverseRootPolynomial.Coordinate) ^ 4 :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Fraction.Order.Arithmetic.pow_nonneg_direct
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 4)
  have cross := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct errorMax fourth)
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum_nonnegative
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment.totalBound fragments)).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct totalMax (Fraction.Order.Arithmetic.mul_nonneg_direct
        fourth tolerancePositive.le))
  have estimate := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct areaMax
      (Fraction.Order.Arithmetic.sq_nonneg_direct (fragments.length : Normalization.InverseRootPolynomial.Coordinate)))
      cross)
      (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
  have bounded : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.fragmentBlockError fragments ≤
      (2 * ((fragments.length : Normalization.InverseRootPolynomial.Coordinate) ^ 2 + 16 * (fragments.length :
        Normalization.InverseRootPolynomial.Coordinate) ^ 4 * bound)) * tolerance :=
    estimate.trans_eq (by ring1)
  have denominatorPositive : 0 < 2 * ((fragments.length : Normalization.InverseRootPolynomial.Coordinate) ^ 2 + 16 *
    (fragments.length : Normalization.InverseRootPolynomial.Coordinate) ^ 4 * bound) + 1 :=
    Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.fragmentCoefficient_nonnegative _ nonnegative)
      (by decide)
  have paid : (2 * ((fragments.length : Normalization.InverseRootPolynomial.Coordinate) ^ 2 + 16 * (fragments.length :
    Normalization.InverseRootPolynomial.Coordinate) ^ 4 * bound) + 1) * tolerance = target := by
    rw [Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ denominatorPositive.ne'
  have strict := Fraction.Order.Arithmetic.add_lt_add_left_direct tolerancePositive
    (2 * ((fragments.length : Normalization.InverseRootPolynomial.Coordinate) ^ 2 + 16 * (fragments.length :
      Normalization.InverseRootPolynomial.Coordinate) ^ 4 * bound) * tolerance)
  rewrite [AddZeroClass.add_zero] at strict
  exact bounded.trans_lt (strict.trans_eq ((by ring1 :
    2 * ((fragments.length : Normalization.InverseRootPolynomial.Coordinate) ^ 2 + 16 * (fragments.length :
      Normalization.InverseRootPolynomial.Coordinate) ^ 4 * bound) * tolerance + tolerance =
      (2 * ((fragments.length : Normalization.InverseRootPolynomial.Coordinate) ^ 2 + 16 * (fragments.length :
        Normalization.InverseRootPolynomial.Coordinate) ^ 4 * bound) + 1) * tolerance).trans paid))

/-- Full flattened path comparison, including its cross-fragment polygon.
The finite maxima are computed from the proved local bounds; no analytic
estimate or equality of differently owned endpoints is an input. -/
theorem owned_fragments_area_bound {evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine}
    {data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.FirstData occurrence index} {otherData :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.SecondData occurrence other index}
    (fragments : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment evaluated data
      otherData)) :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area ((fragments.map
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment.pair).map Prod.fst).flatten -
      Path.PairedIncrementArea.area ((fragments.map
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment.pair).map Prod.snd).flatten) ≤
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.fragmentBlockError fragments := by
  have estimate := Path.PairedBlockComparison.blocks_area_difference_bound (fragments.map
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment.pair)
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum_nonnegative
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment.totalError fragments)
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum_nonnegative
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.OwnedFragment.totalBound fragments)
    (by
      intro pair member
      obtain ⟨fragment, present, rfl⟩ := Data.List.Map.mem_map.mp member
      exact fragment.area_accurate.trans (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.le_maximum _
        present))
    (by
      intro pair member
      obtain ⟨fragment, present, rfl⟩ := Data.List.Map.mem_map.mp member
      exact ⟨fragment.total_accurate.1.trans
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.le_maximum _ present),
        fragment.total_accurate.2.trans (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.le_maximum _
        present)⟩)
    (by
      intro pair member
      obtain ⟨fragment, present, rfl⟩ := Data.List.Map.mem_map.mp member
      exact ⟨fragment.owned_bounded.1.trans (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.le_maximum
        _ present), fragment.owned_bounded.2.trans
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.le_maximum _ present)⟩)
    (by
      intro pair member
      obtain ⟨fragment, present, rfl⟩ := Data.List.Map.mem_map.mp member
      exact ⟨fragment.source_bounded_total.1.trans
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.le_maximum _ present),
        fragment.source_bounded_total.2.trans
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.le_maximum _ present)⟩)
  rwa [Data.List.Map.length_map] at estimate

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
