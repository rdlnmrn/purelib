module
import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Algebra.FiniteSum.Rational.Squares
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.RootRadialBoundary
import Purelib.Riemann.RootContinuation.RootRadialGeometry
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisEnergy
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.Readings.AffineBasisEnergy
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.RootRadialBasisEnergy
import Purelib.Riemann.RootContinuation.RootRadialRefinement
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Riemann.Topology.PreparedSurfacePartitions
import Purelib.Riemann.Topology.PrimitiveSurfaceBudget
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

public section

/-! A shared homogeneous energy request for an actual retained root-chart path. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest

open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Riemann.RootContinuation

variable {genus count : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {edge : Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data edge}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {model :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels.RootModel cell}
  {comparison : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular cell} {target :
    Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}
  {index stage : Nat} {box : Rational.Box}
  {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {sourceSample : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample comparison capSample}

namespace AreaRequest.Evaluation

set_option genInjectivity false in
/-- A paid homogeneous energy request on the actual retained root-chart path.

It caches each segment's basis fan and complete budget, with the original segment order and common radial refinement
depth. -/
structure RequestedBasisEnergy (path : List (Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths.Segment regular model
  sourceSample target floor stage))
    (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box)
      (energyTarget : Normalization.InverseRootPolynomial.Coordinate) (energyFloor : Nat) where
  /-- The original basis polynomial bounds on the radial domain. -/ bounds :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds.RegularBasisBounds polynomials
    RootContinuation.RootRadialGeometry.domain
  /-- The retained whole-path basis request at the original segment count. -/ request :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest.RegularBasisRequest bounds path.length energyTarget
    energyFloor
  /-- The actual radial refinement parameters at the retained request depth. -/ parameters :
    Path.Dyadic.RadialTriangles.Parameters request.depth
  /-- The cached energy entries for the original path segments. -/ entries : List
    (Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisEnergy.AreaRequest.Evaluation.ArcBasisEnergy (basisRequest :=
    request) path parameters)
  /-- The energy entries retain exactly the original ordered path. -/ segments_eq : entries.map
    Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisEnergy.AreaRequest.Evaluation.ArcBasisEnergy.segment = path
  /-- The cached complete homogeneous fan error. -/ error : Normalization.InverseRootPolynomial.Coordinate
  /-- The cached error equals the sum of the actual retained local budgets. -/ error_eq : error =
    FiniteSum.Rational.Squares.coordinateSum (entries.map (fun entry => entry.budget.total))
  /-- The actual cached error equals the original request's total charge. -/ error_total : error = request.total
  /-- The complete retained fan error is strictly below the energy target. -/ error_lt : error < energyTarget

constructive_injectivity RequestedBasisEnergy

namespace RequestedBasisEnergy

variable {path : List (Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths.Segment regular model sourceSample target floor
  stage)}
  {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}
    {energyTarget : Normalization.InverseRootPolynomial.Coordinate} {energyFloor : Nat}

/-- Reuse the supplied basis request and refinement parameters to cache every original segment fan and its paid
aggregate budget. -/
@[expose] def buildWithRequest (path : List (Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths.Segment regular model
  sourceSample target floor stage))
    (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box)
    (geometry : Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisEnergy.AreaRequest.Evaluation.BasisFanGeometry path)
    (bounds : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds.RegularBasisBounds polynomials
      RootContinuation.RootRadialGeometry.domain)
    (request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest.RegularBasisRequest bounds path.length
      energyTarget energyFloor)
    (parameters : Path.Dyadic.RadialTriangles.Parameters request.depth) :
    Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest.AreaRequest.Evaluation.RequestedBasisEnergy path polynomials
      energyTarget energyFloor := by
  let entries := Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisEnergy.AreaRequest.Evaluation.ArcBasisEnergy.buildMany
    path polynomials request geometry parameters
    path (fun _ member => member)
  have segments :=
    Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisEnergy.AreaRequest.Evaluation.ArcBasisEnergy.buildMany_segments path
    polynomials request geometry parameters
    path (fun _ member => member)
  have length : entries.length = path.length := by
    have same := congrArg List.length segments
    rw [List.Map.length_map] at same
    exact same
  let error := FiniteSum.Rational.Squares.coordinateSum (entries.map (fun entry => entry.budget.total))
  have total : error = request.total := by
    have sum := Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisEnergy.AreaRequest.Evaluation.ArcBasisEnergy.budget_sum
      entries
    rw [length] at sum
    exact sum.trans (by rw [request.total_eq]; ring1)
  exact ⟨bounds, request, parameters, entries, segments, error, rfl, total, total.trans_lt request.accurate⟩

/-- Prepare bounds and a sufficient radial request for the original path, then cache its complete basis fan bank. -/
@[expose] def build (path : List (Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths.Segment regular model sourceSample
  target floor stage))
    (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box)
    (geometry : Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisEnergy.AreaRequest.Evaluation.BasisFanGeometry path)
    (energyTarget : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < energyTarget) (energyFloor : Nat) :
    Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest.AreaRequest.Evaluation.RequestedBasisEnergy path polynomials
      energyTarget energyFloor :=
  let bounds := Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds.RegularBasisBounds.build polynomials
    RootContinuation.RootRadialGeometry.domain
  let request := Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest.RegularBasisRequest.build bounds
    path.length energyTarget positive energyFloor
  Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest.AreaRequest.Evaluation.RequestedBasisEnergy.buildWithRequest
    path polynomials geometry bounds request (Path.Dyadic.RadialTriangles.Parameters.build request.depth)

/-- Scalar readback of the retained fan bank. -/
@[expose] def area (energy :
  Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest.AreaRequest.Evaluation.RequestedBasisEnergy path polynomials
  energyTarget energyFloor)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) : Gaussian :=
  Data.Gaussian.Norm.Sum.Basic.gaussianSum (energy.entries.map (fun entry => (entry.budget.sample
    coefficients).boundaryArea))

/-- The actual retained fan area is bounded below by minus the cached error times the coefficient norm. -/
theorem area_lower (energy :
  Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest.AreaRequest.Evaluation.RequestedBasisEnergy path polynomials
  energyTarget energyFloor)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    -(Readings.PreparedObservationCoercivity.coefficientNormSq coefficients * energy.error) ≤ (energy.area
      coefficients).im / 4 := by
  rw [energy.error_eq]
  exact Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisEnergy.AreaRequest.Evaluation.ArcBasisEnergy.sum_lower
    energy.entries coefficients

/-- The actual retained fan area is bounded below by minus the original target times the coefficient norm. -/
theorem area_lower_target (energy :
  Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest.AreaRequest.Evaluation.RequestedBasisEnergy path polynomials
  energyTarget energyFloor)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    -(Readings.PreparedObservationCoercivity.coefficientNormSq coefficients * energyTarget) ≤ (energy.area
      coefficients).im / 4 := open Purelib.Data.Rat in by
  have nonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
    have bound := FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      Normalization.InverseRootPolynomial.Coordinate))
      (fun row => Gaussian.Basic.Canonical.normSq (coefficients row)) (fun row => Gaussian.Basic.Canonical.normSq_nonneg
        (coefficients row))
    rw [FiniteSum.Fin.sumFin_zero] at bound
    exact bound
  exact (Fraction.Order.Arithmetic.neg_le_neg_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct energy.error_lt.le nonnegative)).trans
      (energy.area_lower coefficients)

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest.AreaRequest.Evaluation.RequestedBasisEnergy
  in
set_option genInjectivity false in
/-- Retain the computed boundary area for subsequent joining comparisons. -/
structure Sample (energy :
  Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest.AreaRequest.Evaluation.RequestedBasisEnergy path polynomials
  energyTarget energyFloor)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (first last :
      Normalization.InverseRootPolynomial.Gaussian) where
  /-- The cached actual full fan boundary area. -/ area : Normalization.InverseRootPolynomial.Gaussian
  /-- The area is exactly the finite sum of the retained sampled segment budgets. -/ area_eq : area =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (energy.entries.map (fun entry => (entry.budget.sample
    coefficients).boundaryArea))
  /-- The cached area satisfies its retained homogeneous lower bound. -/ lower :
    -(Readings.PreparedObservationCoercivity.coefficientNormSq coefficients * energy.error) ≤ area.im / 4
  /-- The cached radial potential at the original first endpoint. -/ firstPotential :
    Normalization.InverseRootPolynomial.Gaussian
  /-- The first potential uses the same retained polynomials and radial depth. -/ first_eq : firstPotential =
    RootContinuation.RootRadialGeometry.radialArea (polynomials.value coefficients) energy.request.depth first
  /-- The cached radial potential at the original last endpoint. -/ lastPotential :
    Normalization.InverseRootPolynomial.Gaussian
  /-- The last potential uses the same retained polynomials and radial depth. -/ last_eq : lastPotential =
    RootContinuation.RootRadialGeometry.radialArea (polynomials.value coefficients) energy.request.depth last
  /-- The cached original reversed-segment arc sum. -/ arc : Normalization.InverseRootPolynomial.Gaussian
  /-- The cached arc is exactly the finite sum on the retained original segment endpoints. -/ arc_eq : arc =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (energy.entries.map (fun entry =>
    RootContinuation.RootRadialGeometry.arcArea
    (polynomials.value coefficients) energy.request.depth entry.segment.last.root.coordinate
      entry.segment.first.root.coordinate))
  /-- The full fan area equals its original arc sum plus the last potential minus the first. -/ boundary : area = arc +
    lastPotential - firstPotential

constructive_injectivity Sample

/-- Cache the actual retained fan area, both endpoint radial potentials and the arc sum with their exact boundary
identity. -/
@[expose] def sample (energy :
  Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest.AreaRequest.Evaluation.RequestedBasisEnergy path polynomials
  energyTarget energyFloor)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (first last :
      Normalization.InverseRootPolynomial.Gaussian)
    (chain : Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths.Segment.From first path last) : energy.Sample coefficients
      first last := by
  let area := energy.area coefficients
  have lower := energy.area_lower coefficients
  have chain : Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths.Segment.From first (energy.entries.map
    Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisEnergy.AreaRequest.Evaluation.ArcBasisEnergy.segment)
      last := energy.segments_eq.symm ▸ chain
  let firstPotential := RootContinuation.RootRadialGeometry.radialArea (polynomials.value coefficients)
    energy.request.depth first
  let lastPotential := RootContinuation.RootRadialGeometry.radialArea (polynomials.value coefficients)
    energy.request.depth last
  let arc := area - lastPotential + firstPotential
  have boundary :=
    Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisEnergy.AreaRequest.Evaluation.ArcBasisEnergy.boundary_sum
    energy.entries coefficients chain
  change area = _ at boundary
  refine ⟨area, rfl, lower, firstPotential, rfl, lastPotential, rfl, arc, ?_, ?_⟩
  · dsimp only [arc, firstPotential, lastPotential]
    rw [boundary]
    ring1
  · dsimp only [arc]
    ring1

end RequestedBasisEnergy
end AreaRequest.Evaluation
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest
