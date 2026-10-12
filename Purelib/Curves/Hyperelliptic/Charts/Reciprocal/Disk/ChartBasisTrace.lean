module
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisArcs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest
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
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisBoundary
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisPath
public import Purelib.Integration.Path.HomogeneousTraceConnection
import Init.Prelude
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
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.RootRadialBoundary
import Purelib.Riemann.RootContinuation.RootRadialGeometry
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib.Approximation.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisArcs

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisBoundary.AreaRequest.Evaluation

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisPath

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest.AreaRequest

open Purelib.Integration.Path

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Normalization

public section

/-! Restore a homogeneous trace from the cached chart summary and fan sample. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisTrace

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
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples (Data Sample)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests (Reading)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths (Path Segment)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest.AreaRequest.Evaluation (RequestedBasisEnergy)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse (UniformBounds)
open Purelib.Integration.Path.HomogeneousTraceConnection (HomogeneousTrace)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds (BasisBounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisArcs (basisArcScale)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisArcs.Path (BasisArcGeometry)

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
  {comparison : Data regular cell} {target :
    Coordinate} {floor : Nat}
  {index depth stage : Nat} {box : Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {sample : Sample comparison capSample}
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

namespace RequestedBasisEnergy.Sample

open
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisTrace.AreaRequest.Evaluation.RequestedBasisEnergy.Sample
  in
/-- Restore the homogeneous trace certificate from the exact retained chart summary and original fan sample.

The full endpoint potentials and paid geometric allowance remain explicit, and the original cached summary is reused. -/
@[expose] def trace (energy : Evaluation.RequestedBasisEnergy path.segments polynomials energyTarget energyFloor)
    (basis : ReciprocalPaddedBasisBounds.BasisBounds bounds)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (sampled : energy.Sample coefficients before.root.coordinate after.root.coordinate)
    (summary : IncrementArea.Summary (path.segments.map (fun segment =>
      polynomials.value coefficients segment.last.root.coordinate - polynomials.value coefficients
        segment.first.root.coordinate)))
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (geometry : Path.BasisArcGeometry path slope)
    (allowance : InverseRootPolynomial.Coordinate) (nonnegative : 0 ≤ allowance)
    (paid : Geometric.Basic.quarterRadius (ChartBasisArcs.basisArcScale basis slope) depth ≤ (4 * allowance) ^ 2) :
    HomogeneousTraceConnection.HomogeneousTrace coefficients
      (path.segments.map (fun segment =>
        polynomials.value coefficients segment.last.root.coordinate - polynomials.value coefficients
          segment.first.root.coordinate))
      (polynomials.value coefficients before.root.coordinate) (polynomials.value coefficients after.root.coordinate)
      sampled.firstPotential sampled.lastPotential (energy.error + allowance) := by
  let trace := summary.area + BoundaryRibbon.area
    (polynomials.value coefficients before.root.coordinate) summary.total
  have traceEq : trace = IncrementArea.traceArea (polynomials.value coefficients before.root.coordinate)
      (path.segments.map (fun segment =>
        polynomials.value coefficients segment.last.root.coordinate - polynomials.value coefficients
          segment.first.root.coordinate)) := by
    rw [IncrementArea.traceArea_eq, ← summary.area_eq, ← summary.total_eq]
  have totalEq := summary.total_eq.trans
    (Segment.value_total (polynomials.value coefficients) path.segments path.chain)
  have lower := RequestedBasisEnergy.chart_lower
    energy basis coefficients branch geometry allowance nonnegative paid
  rw [← traceEq, ← sampled.first_eq, ← sampled.last_eq] at lower
  exact ⟨summary, totalEq, trace, traceEq,
    -trace + sampled.lastPotential - sampled.firstPotential, rfl, lower⟩

end RequestedBasisEnergy.Sample
end AreaRequest.Evaluation
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisTrace
