module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartGeometry
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartPath
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinatePolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCoordinateRequest
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartBudget
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedRootGeometry
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Riemann

public section

/-! The retained common reading bank satisfies the geometry needed for its
physical connectors and local odd-degree root fans. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartGeometry

variable {genus count : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {cover : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {covers :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {bounds :
    Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  {depth floor sourceFloor : Nat} {target sourceTarget : Normalization.InverseRootPolynomial.Coordinate}
  {index minimum stage : Nat} {box : Rational.Box}
  {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}
  {anchorBank : Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.PrimitiveCells data index cover.mesh.edges}
  {bank : Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank covers index}
  {basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {joinTarget : Normalization.InverseRootPolynomial.Coordinate} {joinFloor : Nat}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Data.Gaussian.Basic.Canonical

/-- Endpoint containment is retained even when an interval has no neighbour.
Every actual path segment carries containment, step and local sheet sign. -/
@[expose] def Geometry : {intervals : List (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval
  cover covers)} →
    (requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    (plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests) →
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans → Prop
  | _, .nil, _, _ => True
  | _, .cons _ tail, plans, readings =>
      regular.padded.Contains (readings.1.evaluated.first.root.coordinate * readings.1.evaluated.first.root.coordinate)
        ∧
      regular.padded.Contains (readings.1.evaluated.last.root.coordinate * readings.1.evaluated.last.root.coordinate) ∧
      (∀ segment ∈
        (Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartPath.BasisIntervalChartRequest.Plan.Evaluation.path
        readings.1.evaluated).segments,
        Data.Gaussian.Norm.Basic.normSq (segment.last.root.coordinate - segment.first.root.coordinate) <
          collar.coordinateBound / 20 ∧
        0 < segment.first.root.coordinate.re * segment.last.root.coordinate.re +
          segment.first.root.coordinate.im * segment.last.root.coordinate.im ∧
        regular.padded.Contains (segment.first.root.coordinate * segment.first.root.coordinate) ∧
        regular.padded.Contains (segment.last.root.coordinate * segment.last.root.coordinate)) ∧
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartGeometry.Geometry tail plans.2 readings.2

/-- The original quarter-radius coordinate step bound is monotone in its retained slope bound. -/
private theorem step_mono {first last tolerance : Normalization.InverseRootPolynomial.Coordinate} (less : first ≤ last)
  (depth : Nat) :
    2 * (Rational.Geometric.Basic.quarterRadius first depth + 4 * tolerance) ≤ 2 *
      (Rational.Geometric.Basic.quarterRadius last depth + 4 * tolerance) := open Purelib.Data.Rat in by
  have scaled : Rational.Geometric.Basic.quarterRadius first depth ≤ Rational.Geometric.Basic.quarterRadius last depth
    := by
    rw [Rational.Geometric.Basic.quarterRadius_eq_mul_pow, Rational.Geometric.Basic.quarterRadius_eq_mul_pow]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct less (Fraction.Order.Arithmetic.pow_nonneg_direct
      (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 1 / 4) depth)
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct scaled
    le_rfl) (by decide)

/-- The retained common readings satisfy endpoint containment, small steps and positive local sheet signs under the paid
coordinate bounds.

Each interval uses its original root readings and slope bound, with the shared tolerance and depth meeting the retained
clearance conditions. -/
theorem geometry (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (small : target ≤ 1) (padded : target ≤ regular.padded.squareTolerance)
    (clearance : target ≤ collar.coordinateBound / 4) :
    {intervals : List (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover covers)} →
    (requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    (plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests) →
    (readings : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings
      anchorBank bank stage requests plans) →
    (bounds : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCoordinateRequest.BasisCommonCoordinateBounds regular
      intervals) →
    2 * (Rational.Geometric.Basic.quarterRadius bounds.maximum depth + 4 * target) ≤ collar.coordinateBound / 20 →
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartGeometry.Geometry requests plans readings
  | _, .nil, _, _, .nil, _ => True.intro
  | _, .cons _ tail, plans, readings, .cons head remaining, paid => by
      have headPaid := (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartGeometry.step_mono (tolerance := target)
        (Purelib.Data.Rat.Fraction.Order.Basic.le_max_left head.slope remaining.maximum) depth).trans paid
      have tailPaid := (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartGeometry.step_mono (tolerance := target)
        (Purelib.Data.Rat.Fraction.Order.Basic.le_max_right head.slope remaining.maximum) depth).trans paid
      refine
        ⟨IntervalChartGeometry.BasisIntervalChartRequest.Plan.Evaluation.square_inside
        branch padded readings.1.evaluated.first,

          IntervalChartGeometry.BasisIntervalChartRequest.Plan.Evaluation.square_inside
          branch padded readings.1.evaluated.last,
        ?_, Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartGeometry.geometry branch small padded
          clearance tail plans.2 readings.2 remaining tailPaid⟩
      intro segment member
      let coordinate := CoordinatePolynomial.build
        readings.1.sample
      exact
        ⟨(IntervalChartGeometry.BasisIntervalChartRequest.Plan.Evaluation.coordinate_step_bound
        readings.1.evaluated head coordinate branch segment member).trans_le headPaid,

          IntervalChartGeometry.BasisIntervalChartRequest.Plan.Evaluation.coordinate_dot_positive
          readings.1.evaluated head coordinate branch small clearance headPaid segment member,

          IntervalChartGeometry.BasisIntervalChartRequest.Plan.Evaluation.square_inside
          branch padded segment.first,

          IntervalChartGeometry.BasisIntervalChartRequest.Plan.Evaluation.square_inside
          branch padded segment.last⟩

namespace Geometry

/-- Extract both endpoint containment certificates for every original interval from the retained common chart geometry.
-/
theorem inside : {intervals : List (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover
  covers)} →
    (requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    (plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests) → (readings :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans) →
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartGeometry.Geometry requests plans readings →
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank.Inside requests plans readings
  | _, .nil, _, _, _ => True.intro
  | _, .cons _ tail, plans, readings, certified =>
      ⟨certified.1, certified.2.1,
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartGeometry.Geometry.inside tail plans.2
        readings.2 certified.2.2.2⟩

end Geometry

/-- The request is selected before acquisition; arbitrary later spatial
refinement and smaller tolerances use the same geometry certificate. -/
theorem geometry_of_request {intervals : List
  (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover covers)} {spatialFloor : Nat}
    (request : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCoordinateRequest.BasisCommonCoordinateRequest regular
      intervals spatialFloor)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (later : request.depth ≤ depth) (smaller : target ≤ request.tolerance)
    (requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals)
    (plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests) (readings :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans) :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartGeometry.Geometry requests plans readings :=
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartGeometry.geometry branch (smaller.trans request.small)
    (smaller.trans request.padded) (smaller.trans request.clearance)
    requests plans readings request.bounds
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCoordinateRequest.BasisCommonCoordinateRequest.paid_later
      request later smaller)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartGeometry
