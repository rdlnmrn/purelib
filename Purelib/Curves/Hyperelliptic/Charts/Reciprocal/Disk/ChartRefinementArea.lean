module
import Purelib.Algebra.NatCast
import Init.Data.Nat.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Riemann.RootContinuation.RootRadialBoundary
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedArcArea
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcCoarsening
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Riemann.Normalization

open Purelib.Riemann.RootContinuation

public section

/-!
# Requested comparison of refined odd cap arcs with the retained chart edges

The original request pays a uniform bound before choosing its polynomial
stage. Every later radial energy refinement is therefore compared with the
same cached endpoint values, with all original segment counts included.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartRefinementArea

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest (AreaRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest (Evaluation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree (ChartMesh)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths (Segment)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests (Reading)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {edge : Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data edge}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {owners :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.OwnedEndpoints regular cell}
  {comparison : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular cell} {target :
    Coordinate} {floor : Nat}
  {index depth stage minimum : Nat} {box : Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {source : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data index}
  {request : AreaRequest comparison owners target
    floor}
  {charts : ChartMesh request.mesh capSample minimum}
  {original : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells.ComparedCell comparison source capSample
    depth}

universe u

namespace AreaRequest.Evaluation

variable {evaluated : Evaluation charts
  original stage}

/-- In the odd reciprocal chart, the actual cached root coordinate squared lies in the original padded cap box. -/
theorem square_inside (request : ChartAreaRequest.AreaRequest comparison owners target floor)
    (branch : HyperellipticReciprocal.originOrder curve = 1) {parameter : InverseRootPolynomial.Coordinate}
    (reading : VertexRequests.Reading regular owners.model original.sample parameter request.tolerance floor stage) :
    regular.padded.Contains (reading.root.coordinate * reading.root.coordinate) := by
  have square := reading.square
  rw [branch, pow_one, Data.Gaussian.Norm.Basic.normSq_eq_canonical] at square
  exact regular.padded.contains_square
    (ReciprocalExteriorCollar.inverse_inDisk curve (data.boundary.point
      ⟨edge.left.inside.1.trans reading.prepared.inside.1, reading.prepared.inside.2.trans edge.right.inside.2⟩))
    (square.le.trans request.padded_paid)

/-- Each actual retained odd cap segment satisfies the original slope-scaled coordinate step ceiling. -/
private theorem step_le (evaluated : AreaRequest.Evaluation charts original stage)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (segment : VertexPaths.Segment regular owners.model original.sample request.tolerance floor stage)
    (member : segment ∈ evaluated.vertices.path.segments) :
    Data.Gaussian.Norm.Basic.normSq (segment.last.root.coordinate - segment.first.root.coordinate) ≤
      2 * (request.coordinateBounds.slope + 4) * Geometric.Basic.quarterRadius 1 request.spatial.depth := by
  have actual := (Evaluation.coordinate_step_bound evaluated branch segment member).le
  rw [request.coordinateStep_eq] at actual
  have reading := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct request.mesh_paid (by
      decide : (0 : InverseRootPolynomial.Coordinate) ≤ 4)
  exact actual.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add le_rfl reading) (by
    decide)).trans_eq
    (by simp only [Geometric.Basic.quarterRadius, Fraction.Field.div_eq_mul_inv_direct]; ring1))

/-- Any finite radial refinement of one actual retained odd cap segment stays within the original paid area ceiling. -/
private theorem arc_error (evaluated : AreaRequest.Evaluation charts original stage)
    (branch : HyperellipticReciprocal.originOrder curve = 1) (energyDepth : Nat)
    (segment : VertexPaths.Segment regular owners.model original.sample request.tolerance floor stage)
    (member : segment ∈ evaluated.vertices.path.segments) :
    Data.Gaussian.Norm.Basic.normSq (RootRadialGeometry.arcArea capSample.primitive.value.eval energyDepth
      segment.last.root.coordinate segment.first.root.coordinate -
      BoundaryRibbon.area segment.last.chartValue segment.first.chartValue) ≤
        request.energyScale * Geometric.Basic.quarterRadius 1 request.spatial.depth ^ 2 := by
  have lastValue := segment.last.chart_eq
  rw [branch, if_neg (by decide : (1 : Nat) ≠ 0)] at lastValue
  have firstValue := segment.first.chart_eq
  rw [branch, if_neg (by decide : (1 : Nat) ≠ 0)] at firstValue
  rw [lastValue, firstValue]
  have estimate := request.energyBounds.arc_refinement capSample branch
    (square_inside request branch
      segment.last)
      (square_inside request
      branch segment.first) energyDepth
  rw [show segment.first.root.coordinate - segment.last.root.coordinate =
    -(segment.last.root.coordinate - segment.first.root.coordinate) by ring1, Data.Gaussian.Norm.Basic.normSq_neg]
      at estimate
  have bounded := Fraction.Order.Arithmetic.pow_le_pow_direct (Data.Gaussian.Norm.Basic.normSq_nonneg _)
    (step_le evaluated branch
      segment member) 2
  exact estimate.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bounded
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 16)
      (Fraction.Order.Arithmetic.sq_nonneg_direct _))).trans_eq (by rw [request.energyScale_eq]; ring1))

/-- The full requested comparison holds for every finite energy depth. Its coefficient ceiling and original segment
count were paid before the shared source polynomial was selected. -/
theorem refined_arc_error (evaluated : AreaRequest.Evaluation charts original stage)
    (branch : HyperellipticReciprocal.originOrder curve = 1) (energyDepth : Nat) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (evaluated.vertices.path.segments.map (fun segment =>
      RootRadialGeometry.arcArea capSample.primitive.value.eval energyDepth segment.last.root.coordinate
        segment.first.root.coordinate)) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (evaluated.vertices.path.segments.map (fun segment =>
        BoundaryRibbon.area segment.last.chartValue segment.first.chartValue))) < target := by
  let errors := evaluated.vertices.path.segments.map (fun segment =>
    RootRadialGeometry.arcArea capSample.primitive.value.eval energyDepth segment.last.root.coordinate
      segment.first.root.coordinate -
      BoundaryRibbon.area segment.last.chartValue segment.first.chartValue)
  have scaleNonnegative : 0 ≤ request.energyScale := by
    rw [request.energyScale_eq]
    exact Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 64)
        (Fraction.Order.Arithmetic.sq_nonneg_direct _)) (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have errorNonnegative : 0 ≤ request.energyScale * Geometric.Basic.quarterRadius 1 request.spatial.depth ^ 2 :=
    Fraction.Order.Arithmetic.mul_nonneg_direct scaleNonnegative (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have each : ∀ value ∈ errors, Data.Gaussian.Norm.Basic.normSq value ≤ request.energyScale *
    Geometric.Basic.quarterRadius 1 request.spatial.depth ^ 2 := by
    intro value member
    dsimp only [errors] at member
    rcases Map.mem_map.mp member with ⟨segment, segmentMember, rfl⟩
    exact arc_error evaluated
      branch energyDepth segment segmentMember
  have length : errors.length ≤ 2 ^ request.spatial.depth := by
    rw [Map.length_map, evaluated.vertices.path.count_eq]
  have estimate := IncrementArea.sum_bound_of_length errorNonnegative each length
  dsimp only [errors] at estimate
  rw [Data.Gaussian.Norm.Sum.Basic.gaussianSum_map_sub] at estimate
  apply estimate.trans_lt
  have unitCancel : (((2 ^ request.spatial.depth : Nat) : InverseRootPolynomial.Coordinate) ^ 2) *
      Geometric.Basic.quarterRadius 1 request.spatial.depth = 1 := by
    have square : (((2 ^ request.spatial.depth : Nat) : InverseRootPolynomial.Coordinate) ^ 2) =
        (4 : InverseRootPolynomial.Coordinate) ^ request.spatial.depth := by
      rw [Algebra.NatCast.pow, Nat.cast_ofNat]
      calc
        _ = (2 : InverseRootPolynomial.Coordinate) ^ (request.spatial.depth * 2) :=
          (pow_mul (2 : InverseRootPolynomial.Coordinate) request.spatial.depth 2).symm
        _ = (2 : InverseRootPolynomial.Coordinate) ^ (2 * request.spatial.depth) :=
          congrArg (fun exponent => (2 : InverseRootPolynomial.Coordinate) ^ exponent)
            (Nat.mul_comm request.spatial.depth 2)
        _ = ((2 : InverseRootPolynomial.Coordinate) ^ 2) ^ request.spatial.depth :=
          pow_mul (2 : InverseRootPolynomial.Coordinate) 2 request.spatial.depth
        _ = _ := congrArg (fun value : InverseRootPolynomial.Coordinate => value ^ request.spatial.depth)
          (by decide : (2 : InverseRootPolynomial.Coordinate) ^ 2 = 4)
    rw [square, Geometric.Basic.quarterRadius]
    exact (Fraction.Field.mul_comm _ _).trans
      (Fraction.Field.div_mul_cancel_of_ne _ _
        (Fraction.Order.Arithmetic.pow_pos_direct (by decide) request.spatial.depth).ne')
  have paid : (((2 ^ request.spatial.depth : Nat) : InverseRootPolynomial.Coordinate) ^ 2) *
      (request.energyScale * Geometric.Basic.quarterRadius 1 request.spatial.depth ^ 2) = Geometric.Basic.quarterRadius
        request.energyScale request.spatial.depth := by
    calc
      _ = ((((2 ^ request.spatial.depth : Nat) : InverseRootPolynomial.Coordinate) ^ 2) * Geometric.Basic.quarterRadius
        1 request.spatial.depth) *
        (request.energyScale * Geometric.Basic.quarterRadius 1 request.spatial.depth) := by ring1
      _ = _ := by
        rw [unitCancel]; simp only [Geometric.Basic.quarterRadius, Fraction.Field.div_eq_mul_inv_direct]; ring1
  exact paid.trans_lt request.energy_paid

end AreaRequest.Evaluation
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartRefinementArea
