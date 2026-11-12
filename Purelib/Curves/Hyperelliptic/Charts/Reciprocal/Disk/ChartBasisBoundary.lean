module
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.RootRadialBoundary
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisArcs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.RootRadialGeometry
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Approximation.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisArcs

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisEnergy.AreaRequest.Evaluation

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest.AreaRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

open Purelib.Riemann.Topology

public section

/-! Signed homogeneous energy comparison with the retained root-chart trace. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisBoundary

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Algebra.FiniteSum.Rational.Squares (coordinateSum)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds (RegularBasisBounds)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest (RegularBasisRequest)
open Purelib.Riemann.Readings.AffineBasisEnergy (AffineBasis)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples (Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests (Reading)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths (Segment Path)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest.AreaRequest.Evaluation (RequestedBasisEnergy)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisEnergy.AreaRequest.Evaluation (ArcBasisEnergy)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisArcs (basisArcScale)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse (UniformBounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds (BasisBounds)
open Purelib.Riemann.RootContinuation

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {edge : ParameterEdge} {cell :
    Cell data edge}
  {regular : RegularBounds.Data cap} {model :
    RootModel cell}
  {comparison : Data regular cell} {target :
    Coordinate} {floor : Nat}
  {index depth stage : Nat} {box : Geometry.Rational.Box}
  {capSample : Cap.Primitives.Sample cap differential index box}
  {sample : ArcSamples.Sample comparison capSample}
  {first last : Coordinate}
  {before : Reading regular model sample first target
    floor stage}
  {after : Reading regular model sample last target
    floor stage}
  {path : Path regular model sample target floor stage
    depth before after}
  {bounds : UniformBounds regular.padded} {slope
    : Coordinate}

namespace AreaRequest.Evaluation

variable {polynomials :
  RegularBasisPolynomials cap index box}
  {energyTarget : Coordinate} {energyFloor : Nat}

/-- The reversed endpoint-wedge sum on the actual retained root chain is the negative full trace area of its original
increments. -/
private theorem reverse_basis_trace (values : Gaussian → Gaussian)
    (segments : List (Segment regular model sample target floor stage))
    {first last : Gaussian} (chain : Segment.From first segments last) :
    gaussianSum (segments.map (fun segment =>
      BoundaryRibbon.area
      (values segment.last.root.coordinate) (values segment.first.root.coordinate))) =
    -IncrementArea.traceArea (values first) (segments.map (fun segment =>
      values segment.last.root.coordinate - values segment.first.root.coordinate)) := by
  induction segments generalizing first with
  | nil => change (0 : Gaussian) = -0; ring1
  | cons head tail ih =>
      change first = head.first.root.coordinate ∧ Segment.From head.last.root.coordinate tail last at chain
      change BoundaryRibbon.area (values head.last.root.coordinate) (values head.first.root.coordinate) +
        gaussianSum (tail.map (fun segment => BoundaryRibbon.area (values
          segment.last.root.coordinate) (values segment.first.root.coordinate))) =
        -(BoundaryRibbon.area (values first) (values first + (values head.last.root.coordinate - values
          head.first.root.coordinate)) +
          IncrementArea.traceArea (values first + (values head.last.root.coordinate - values
            head.first.root.coordinate))
            (tail.map (fun segment => values segment.last.root.coordinate - values segment.first.root.coordinate)))
      rw [chain.1, show values head.first.root.coordinate + (values head.last.root.coordinate - values
        head.first.root.coordinate) =
        values head.last.root.coordinate by ring1, ih chain.2]
      unfold BoundaryRibbon.area
      ring1

namespace RequestedBasisEnergy

/-- Compare the cached homogeneous fan area with the signed trace on its actual root-coordinate chain. Both radial
endpoints retain their signs. -/
theorem chart_boundary_bound (energy : RequestedBasisEnergy path.segments polynomials energyTarget
  energyFloor)
    (basis : BasisBounds bounds)
    (coefficients : GaussianVector genus)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (geometry : Path.BasisArcGeometry path slope) :
    Data.Gaussian.Norm.Basic.normSq (energy.area coefficients -
      (-IncrementArea.traceArea (polynomials.value coefficients before.root.coordinate)
        (path.segments.map (fun segment =>
          polynomials.value coefficients segment.last.root.coordinate - polynomials.value coefficients
            segment.first.root.coordinate)) +
        RootRadialGeometry.radialArea (polynomials.value coefficients) energy.request.depth after.root.coordinate -
        RootRadialGeometry.radialArea (polynomials.value coefficients) energy.request.depth before.root.coordinate)) ≤
      Geometric.Basic.quarterRadius (basisArcScale basis slope) depth *
        (coefficientNormSq coefficients) ^ 2 := by
  have mapped := congrArg (List.map (fun segment => RootRadialGeometry.arcArea (polynomials.value coefficients)
    energy.request.depth
    segment.last.root.coordinate segment.first.root.coordinate)) energy.segments_eq
  rw [Data.List.Map.map_map] at mapped
  dsimp only [Function.comp_def] at mapped
  have bound := Path.basis_refined_arc_error path (polynomials := polynomials) basis coefficients branch
    energy.request.depth
    geometry
  rw [reverse_basis_trace
    (polynomials.value coefficients) path.segments path.chain] at bound
  have chain : Segment.From before.root.coordinate (energy.entries.map ArcBasisEnergy.segment)
      after.root.coordinate := energy.segments_eq.symm ▸ path.chain
  have boundary := ArcBasisEnergy.boundary_sum energy.entries coefficients chain
  rw [mapped] at boundary
  change energy.area coefficients = _ at boundary
  rw [boundary]
  exact (congrArg Data.Gaussian.Norm.Basic.normSq (by ring1)).trans_le bound

/-- A linear loss allowance transports the homogeneous lower bound to the same trace; this leaves the endpoint
correction available for gluing. -/
theorem chart_lower (energy : RequestedBasisEnergy path.segments polynomials energyTarget energyFloor)
    (basis : BasisBounds bounds)
    (coefficients : GaussianVector genus)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (geometry : Path.BasisArcGeometry path slope)
    (allowance : Coordinate) (nonnegative : 0 ≤ allowance)
    (paid : Geometric.Basic.quarterRadius (basisArcScale basis slope) depth ≤ (4 * allowance) ^ 2) :
    -((energy.error + allowance) * coefficientNormSq coefficients) ≤
      (-IncrementArea.traceArea (polynomials.value coefficients before.root.coordinate)
        (path.segments.map (fun segment =>
          polynomials.value coefficients segment.last.root.coordinate - polynomials.value coefficients
            segment.first.root.coordinate)) +
        RootRadialGeometry.radialArea (polynomials.value coefficients) energy.request.depth after.root.coordinate -
        RootRadialGeometry.radialArea (polynomials.value coefficients) energy.request.depth before.root.coordinate).im /
          4 := by
  have coefficientNonnegative : 0 ≤ coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
      (Order.Positivity.sumFin_mono (fun _ => (0 : Coordinate)) _ (fun row =>
        normSq_nonneg (coefficients row)))
  have estimate :=
    (chart_boundary_bound
    energy basis coefficients branch geometry).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct paid (Fraction.Order.Arithmetic.sq_nonneg_direct _))
  have comparison := PreparedSurfaceCoercivity.boundaryEnergy_sub_budget_le (energy.area coefficients) _
    (allowance * coefficientNormSq coefficients)
    (Fraction.Order.Arithmetic.mul_nonneg_direct nonnegative coefficientNonnegative)
    (estimate.trans_eq (by ring1))
  have lower := Fraction.Order.Arithmetic.sub_le_sub_right_direct (energy.area_lower coefficients)
    (allowance * coefficientNormSq coefficients)
  exact (show -((energy.error + allowance) * coefficientNormSq coefficients) =
    -(coefficientNormSq coefficients * energy.error) - allowance *
      coefficientNormSq coefficients by ring1).trans_le
      (lower.trans comparison)

end RequestedBasisEnergy
end AreaRequest.Evaluation
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisBoundary
