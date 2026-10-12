module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinatePolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartPath
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinateVariation
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedRootGeometry
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib

open Purelib.Approximation.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition.BasisIntervalChartRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartPath.BasisIntervalChartRequest.Plan

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinateVariation

open Purelib.Data.Rat

open Purelib.Riemann.Normalization

public section

/-! Geometry of the actual common-interval root readings, on their retained
anchor cell and polynomial bank. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartGeometry

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRequests (BasisSourceRequest)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest (BasisIntervalChartRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition.BasisIntervalChartRequest (Plan)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest.BasisIntervalChartRequest (Model)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests (Reading)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths (Segment)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Point (ReadingView)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonInterval)
open _root_.Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinatePolynomial (CoordinateBounds)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {edge : ParameterEdge} {cell :
    Cell data edge}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {model :
    RootModel cell}
  {parameter target sourceTarget : Coordinate} {floor sourceFloor :
    Nat}
  {covers : BasisSourceCovers parent}

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)

variable {cover : Cover data}

namespace BasisIntervalChartRequest

variable {interval : BasisCommonInterval cover
  covers} {depth index minimum : Nat} {box : Purelib.Geometry.Rational.Box}
  {request : BasisIntervalChartRequest
    interval regular depth target sourceTarget floor sourceFloor}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {polynomials : RegularBasisPolynomials cap
    index box}

namespace Plan.Evaluation

variable {plan :
  Plan
  request capSample polynomials minimum}
  {comparison : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular interval.anchor.cell}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample comparison capSample}
  {bank : BasisSourceLocations.SampleBank
    covers index} {stage : Nat}

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)

/-- The square certificate refers to the physical parent parameter even when the chart is restricted to a smaller common
interval. -/
theorem square_inside (branch : HyperellipticReciprocal.originOrder curve = 1)
    (paid : target ≤ regular.padded.squareTolerance) {parameter : InverseRootPolynomial.Coordinate}
    (reading : VertexRequests.Reading regular (BasisIntervalChartRequest.Model interval) sample parameter target floor
      stage) :
    regular.padded.Contains (reading.root.coordinate * reading.root.coordinate) := by
  have square := reading.square
  rw [branch, pow_one] at square
  exact regular.padded.contains_square
    (ReciprocalExteriorCollar.inverse_inDisk curve (data.boundary.point
      ⟨interval.anchor.owner.left.inside.1.trans reading.prepared.inside.1,
        reading.prepared.inside.2.trans interval.anchor.owner.right.inside.2⟩))
    (by
      have scalar := square.le.trans paid
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
      exact scalar)

/-- Use the acquired path width, not the width of its larger anchor cell. -/
theorem coordinate_step_bound (evaluated : Plan.Evaluation plan sample bank stage)
    (bounds : CoordinatePolynomial.CoordinateBounds comparison)
    (coordinate : CoordinatePolynomial sample)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (segment : VertexPaths.Segment regular (BasisIntervalChartRequest.Model interval) sample target floor stage)
    (member : segment ∈ (Evaluation.path evaluated).segments) :
    Data.Gaussian.Norm.Basic.normSq (segment.last.root.coordinate - segment.first.root.coordinate) <
      2 * (Geometric.Basic.quarterRadius bounds.slope depth + 4 * target) := by
  have widthLe : interval.edge.right.parameter - interval.edge.left.parameter ≤ 1 := by
    exact (Fraction.Order.Arithmetic.sub_le_sub_direct
      interval.edge.right.inside.2 interval.edge.left.inside.1).trans_eq
      (show (1 : Fraction.Rational) - 0 = 1 by decide)
  have widthSquare : (interval.edge.right.parameter - interval.edge.left.parameter)^2 ≤ 1 :=
    (Fraction.Order.Arithmetic.pow_le_pow_direct (Fraction.Order.Arithmetic.sub_nonneg_direct interval.ordered) widthLe
      2).trans_eq (one_pow _)
  have bounded := Path.coordinate_increment_bound (Evaluation.path evaluated) bounds coordinate branch segment member
  have upper := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct widthSquare
    (Geometric.Basic.quarterRadius_nonneg bounds.slope_nonnegative depth)
  rw [Fraction.Field.mul_one_direct] at upper
  exact bounded.trans_le (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct upper le_rfl) (by decide))

/-- Consecutive acquired root coordinates have positive Euclidean dot product when the retained step, clearance and
error bounds are paid. -/
theorem coordinate_dot_positive (evaluated : Plan.Evaluation plan sample bank stage)
    (bounds : CoordinatePolynomial.CoordinateBounds comparison)
    (coordinate : CoordinatePolynomial sample)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (small : target ≤ 1) (clearance : target ≤ collar.coordinateBound / 4)
    (paid : 2 * (Geometric.Basic.quarterRadius bounds.slope depth + 4 * target) ≤ collar.coordinateBound / 20)
    (segment : VertexPaths.Segment regular (BasisIntervalChartRequest.Model interval) sample target floor stage)
    (member : segment ∈ (Evaluation.path evaluated).segments) :
    0 < segment.first.root.coordinate.re * segment.last.root.coordinate.re +
      segment.first.root.coordinate.im * segment.last.root.coordinate.im :=
  Segment.coordinate_dot_positive segment branch small clearance

      ((coordinate_step_bound
      evaluated bounds coordinate branch segment member).trans_le paid)

end Plan.Evaluation
end BasisIntervalChartRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartGeometry
