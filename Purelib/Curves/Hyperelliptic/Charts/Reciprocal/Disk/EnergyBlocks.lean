module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.RootContinuation.RootRadialBoundary
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergyBoundary
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcCoarsening
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.RootRadialGeometry
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib

open Purelib.Data.Rat

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

public section

/-!
# Cached odd cap energy blocks

Each block comes from an actual chart evaluation and its generated fans.
The restored connection consumes these cached radial endpoints and errors
without evaluating a polynomial or radial path again.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyBlocks

open Purelib.Data.Gaussian.Basic.Canonical

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {index : Nat} {box : Rational.Box} {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap
    differential index box}

set_option genInjectivity false in
/-- A cached odd-cap chart energy with its original path, radial endpoints and paid error.

Keep the actual sample, depth, endpoint evaluations, finite path summary and imaginary-energy lower bound. -/
structure EnergyBlock (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box)
    (depth : Nat) (target energyTarget : Normalization.InverseRootPolynomial.Coordinate) where
  /-- The original first retained root-coordinate reading. -/ firstRoot : Normalization.InverseRootPolynomial.Gaussian
  /-- The original final retained root-coordinate reading. -/ lastRoot : Normalization.InverseRootPolynomial.Gaussian
  /-- The original chart value at the retained first root reading. -/ firstValue :
    Normalization.InverseRootPolynomial.Gaussian
  /-- The original chart value at the retained final root reading. -/ lastValue :
    Normalization.InverseRootPolynomial.Gaussian
  /-- The retained first value is exactly the original sample polynomial evaluated at its first root. -/ first_value :
    firstValue = sample.primitive.value.eval firstRoot
  /-- The retained final value is exactly the original sample polynomial evaluated at its final root. -/ last_value :
    lastValue = sample.primitive.value.eval lastRoot
  /-- The retained original radial area at the first root and shared depth. -/ firstRadial :
    Normalization.InverseRootPolynomial.Gaussian
  /-- The retained original radial area at the final root and shared depth. -/ lastRadial :
    Normalization.InverseRootPolynomial.Gaussian
  /-- The first radial value equals its exact original finite radial-area computation. -/ first_radial : firstRadial =
    RootContinuation.RootRadialGeometry.radialArea sample.primitive.value.eval depth firstRoot
  /-- The final radial value equals its exact original finite radial-area computation. -/ last_radial : lastRadial =
    RootContinuation.RootRadialGeometry.radialArea sample.primitive.value.eval depth lastRoot
  /-- The original complete chart increment path. -/ path : List Normalization.InverseRootPolynomial.Gaussian
  /-- The finite area summary of the exact retained chart path. -/ summary : Path.IncrementArea.Summary path
  /-- The retained path total equals the original last chart value minus the first. -/ total_eq : summary.total =
    lastValue - firstValue
  /-- The actual retained fan energy. -/ energy : Normalization.InverseRootPolynomial.Gaussian
  /-- The retained imaginary fan energy divided by four is at least minus the energy target. -/ lower : -energyTarget ≤
    energy.im / 4
  /-- The retained fan-minus-boundary Gaussian residual. -/ error : Normalization.InverseRootPolynomial.Gaussian
  /-- The residual is exactly fan energy minus the original path, endpoint and radial boundary expression. -/ error_eq :
    error = energy - (-summary.area - Path.BoundaryRibbon.area firstValue lastValue + lastRadial - firstRadial)
  /-- The retained residual squared norm is at most the original comparison target. -/ bounded :
    Data.Gaussian.Norm.Basic.normSq error ≤ target

constructive_injectivity EnergyBlock

namespace EnergyBlock

variable {count : Nat} {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {edge : Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data edge}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {owners :
    Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.OwnedEndpoints regular cell}
  {comparison : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular cell} {target energyTarget :
    Normalization.InverseRootPolynomial.Coordinate} {floor energyFloor : Nat}
  {depth stage minimum energyDepth : Nat} {source :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data index}
  {request : Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest comparison owners target floor} {charts :
    Hyperelliptic.Charts.Reciprocal.Disk.VertexTree.ChartMesh request.mesh sample minimum}
  {original : Hyperelliptic.Charts.Reciprocal.Disk.ParentCells.ComparedCell comparison source sample depth}

/-- Package the original chart evaluation and requested fan energy at the retained common depth. -/
@[expose] def build (evaluated : Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest.Evaluation charts
  original stage)
    (energy : Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy.AreaRequest.Evaluation.RequestedEnergy evaluated
      energyTarget energyFloor)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) (sameDepth :
      energy.request.depth = energyDepth) :
    Hyperelliptic.Charts.Reciprocal.Disk.EnergyBlocks.EnergyBlock sample energyDepth target energyTarget := by
  let firstRadial := RootContinuation.RootRadialGeometry.radialArea sample.primitive.value.eval energyDepth
    evaluated.vertices.first.root.coordinate
  let terminalRadial := RootContinuation.RootRadialGeometry.radialArea sample.primitive.value.eval energyDepth
    evaluated.vertices.last.root.coordinate
  let error := energy.area - (-evaluated.vertices.path.chart.area - Path.BoundaryRibbon.area
    evaluated.vertices.first.chartValue evaluated.vertices.last.chartValue +
    terminalRadial - firstRadial)
  have estimate :=
    Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergyBoundary.AreaRequest.Evaluation.RequestedEnergy.chart_boundary_close
    energy branch
  rw [sameDepth] at estimate
  refine ⟨evaluated.vertices.first.root.coordinate, evaluated.vertices.last.root.coordinate,
    evaluated.vertices.first.chartValue, evaluated.vertices.last.chartValue, ?_, ?_,
    firstRadial, terminalRadial, rfl, rfl, evaluated.vertices.path.chartPath, evaluated.vertices.path.chart,
    evaluated.vertices.path.chart_total, energy.area, energy.lower.le, error, rfl, estimate.le⟩
  · have value := evaluated.vertices.first.chart_eq
    rewrite [branch, if_neg (by decide : ¬ (1 : Nat) = 0)] at value
    exact value
  · have value := evaluated.vertices.last.chart_eq
    rewrite [branch, if_neg (by decide : ¬ (1 : Nat) = 0)] at value
    exact value

end EnergyBlock
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyBlocks
