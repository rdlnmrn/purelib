module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisArcs
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.RootRadialBoundary
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisBoundary
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisGeometry
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcCoarsening
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinatePolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
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

open Purelib

open Purelib.Approximation.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisBoundary.AreaRequest.Evaluation

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisGeometry.AreaRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest.AreaRequest

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

public section

/-! Retained scalar allowance for a homogeneous chart boundary comparison. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisBudget

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
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners (OwnedEndpoints)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples (Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (SourcePrimitive)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells (ComparedCell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest (AreaRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest (Evaluation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree (ChartMesh)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest.AreaRequest.Evaluation (RequestedBasisEnergy)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisArcs (basisArcScale)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse (UniformBounds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds (BasisBounds)
open Purelib.Riemann.RootContinuation

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {edge : ParameterEdge} {cell :
    Cell data edge}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {owners :
    OwnedEndpoints regular cell}
  {comparison : Data regular cell} {target :
    Coordinate} {floor : Nat}
  {index depth stage minimum : Nat} {box : Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {source : SourcePrimitive data index}
  {request : AreaRequest comparison owners target
    floor}
  {charts : ChartMesh request.mesh capSample minimum}
  {original : ComparedCell comparison source capSample
    depth}

namespace AreaRequest.Evaluation

variable {evaluated : Evaluation charts
  original stage}
  {polynomials : RegularBasisPolynomials cap
    index box} {energyTarget : Coordinate} {energyFloor : Nat}

set_option genInjectivity false in
/-- A cached, coefficient-independent allowance for this retained chart. -/
structure BasisBoundaryBudget (evaluated : AreaRequest.Evaluation charts original stage) where
  /-- The retained coefficient-independent basis bounds on the original chart energy request. -/ basis :
    ReciprocalPaddedBasisBounds.BasisBounds request.energyBounds
  /-- The cached scalar allowance for this actual chart boundary comparison. -/ bound : InverseRootPolynomial.Coordinate
  /-- The allowance is the exact original basis arc scale at the retained spatial refinement depth. -/ bound_eq : bound
    = Geometric.Basic.quarterRadius (ChartBasisArcs.basisArcScale basis request.coordinateBounds.slope)
    request.spatial.depth
  /-- The actual cached chart boundary allowance is nonnegative. -/ nonnegative : 0 ≤ bound
  /-- The original chart request pays the cached boundary allowance strictly below its target. -/ paid : bound < target

constructive_injectivity BasisBoundaryBudget

namespace BasisBoundaryBudget

/-- Cache the original retained basis bounds and paid geometric radius without acquiring new chart samples. -/
@[expose] def build (evaluated : AreaRequest.Evaluation charts original stage) :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisBudget.AreaRequest.Evaluation.BasisBoundaryBudget evaluated :=
  by
  let basis := request.basisBounds
  let bound := Geometric.Basic.quarterRadius (ChartBasisArcs.basisArcScale basis request.coordinateBounds.slope)
    request.spatial.depth
  have nonnegative : 0 ≤ ChartBasisArcs.basisArcScale basis request.coordinateBounds.slope :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (Fraction.Order.Arithmetic.sq_nonneg_direct _))
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have paid : bound < target := by
    change Geometric.Basic.quarterRadius (64 * request.basisBounds.coefficient^2 * (request.coordinateBounds.slope +
      4)^2) request.spatial.depth < target
    rw [← request.basisScale_eq]
    exact request.basis_paid
  exact ⟨basis, bound, rfl, Geometric.Basic.quarterRadius_nonneg nonnegative _, paid⟩

/-- The actual chart basis energy differs from its full oriented trace-and-radial boundary by the retained allowance
times the squared coefficient norm. -/
theorem accurate (budget :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisBudget.AreaRequest.Evaluation.BasisBoundaryBudget evaluated)
    (energy : Evaluation.RequestedBasisEnergy evaluated.vertices.path.segments polynomials energyTarget energyFloor)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (branch : HyperellipticReciprocal.originOrder
      curve = 1) :
    Data.Gaussian.Norm.Basic.normSq (energy.area coefficients -
      (-IncrementArea.traceArea (polynomials.value coefficients evaluated.vertices.first.root.coordinate)
        (evaluated.vertices.path.segments.map (fun segment =>
          polynomials.value coefficients segment.last.root.coordinate - polynomials.value coefficients
            segment.first.root.coordinate)) +
        RootRadialGeometry.radialArea (polynomials.value coefficients) energy.request.depth
          evaluated.vertices.last.root.coordinate -
        RootRadialGeometry.radialArea (polynomials.value coefficients) energy.request.depth
          evaluated.vertices.first.root.coordinate)) ≤
      budget.bound * (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  rw [budget.bound_eq]
  exact RequestedBasisEnergy.chart_boundary_bound
    energy budget.basis coefficients branch
      (Evaluation.basisArcGeometry evaluated branch)

end BasisBoundaryBudget
end AreaRequest.Evaluation
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisBudget
