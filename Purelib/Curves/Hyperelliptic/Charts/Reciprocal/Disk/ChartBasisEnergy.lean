module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Rational.Squares
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Energy.AffineTriangle

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
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
import Purelib.Riemann.Readings.AffineBasisEnergy
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.RootRadialBasisEnergy
public import Purelib.Riemann.RootContinuation.RootRadialBasisRequest
public import Purelib.Riemann.RootContinuation.RootRadialBoundary
import Purelib.Riemann.RootContinuation.RootRadialGeometry
import Purelib.Riemann.RootContinuation.RootRadialRefinement
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Riemann.RootContinuation.RootRadialBasisBoundary
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
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
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

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

public section

/-! Homogeneous fan data on every actual retained odd chart segment.
Internal radial terms cancel through the retained coordinate chain. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisEnergy

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Riemann.RootContinuation.RootRadialGeometry
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
  {sample : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample comparison capSample}

namespace AreaRequest.Evaluation

/-- The fan needs only the actual segment coordinates and their finite geometry. -/
@[expose] def BasisFanGeometry (segments : List (Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths.Segment regular model
  sample target floor stage)) : Prop :=
  ∀ segment ∈ segments,
    Data.Gaussian.Norm.Basic.normSq segment.last.root.coordinate ≤ 2 ∧ Data.Gaussian.Norm.Basic.normSq
      segment.first.root.coordinate ≤ 2 ∧
    0 ≤ Energy.AffineTriangle.crossEnergy segment.last.root.coordinate segment.first.root.coordinate

variable {path : List (Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths.Segment regular model sample target floor
  stage)}
  {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}
  {bounds : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds.RegularBasisBounds polynomials
    RootContinuation.RootRadialGeometry.domain}
  {number energyFloor : Nat} {energyTarget : Normalization.InverseRootPolynomial.Coordinate}
  {basisRequest : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest.RegularBasisRequest bounds number
    energyTarget energyFloor}
  {parameters : Path.Dyadic.RadialTriangles.Parameters basisRequest.depth}

set_option genInjectivity false in
/-- One original fan segment's radial refinement, cached basis values and paid surface budget.

The segment membership and exact total charge bind the energy comparison to the same retained fan. -/
structure ArcBasisEnergy (path : List (Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths.Segment regular model sample
  target floor stage))
    (parameters : Path.Dyadic.RadialTriangles.Parameters basisRequest.depth) where
  /-- The original retained fan segment. -/ segment : Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths.Segment regular
    model sample target floor stage
  /-- This segment belongs to the original evaluated fan. -/ member : segment ∈ path
  /-- The actual radial refinement at its original endpoints. -/ refinement :
    RootContinuation.RootRadialRefinement.Refinement segment.last.root.coordinate segment.first.root.coordinate
    parameters
  /-- The cached basis values on this same refinement. -/ values : RootContinuation.RootRadialBasisEnergy.BasisValues
    refinement polynomials
  /-- The retained local surface budget. -/ budget : Readings.AffineBasisEnergy.AffineBasis.SurfaceBudget values.basis
  /-- The budget total is exactly the fixed original coefficient scale times the local tolerance. -/ budget_total :
    budget.total = 128 * (2 * bounds.coefficient + 3) * basisRequest.tolerance.epsilon

constructive_injectivity ArcBasisEnergy

namespace ArcBasisEnergy

/-- Prepare the actual segment refinement and cache its basis values and surface budget from the supplied fan geometry.
-/
@[expose] def build (path : List (Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths.Segment regular model sample target
  floor stage))
    (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box)
    {bounds : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds.RegularBasisBounds polynomials
      RootContinuation.RootRadialGeometry.domain}
    (basisRequest : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest.RegularBasisRequest bounds number
      energyTarget energyFloor)
    (geometry : Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisEnergy.AreaRequest.Evaluation.BasisFanGeometry path)
    (parameters : Path.Dyadic.RadialTriangles.Parameters basisRequest.depth)
    (segment : Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths.Segment regular model sample target floor stage)
    (member : segment ∈ path) :
      Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisEnergy.AreaRequest.Evaluation.ArcBasisEnergy (basisRequest :=
      basisRequest) path parameters := by
  have bounds := geometry segment member
  let refinement := RootContinuation.RootRadialRefinement.Refinement.build bounds.1 bounds.2.1 bounds.2.2 parameters
  let values := RootContinuation.RootRadialBasisEnergy.BasisValues.build refinement polynomials
  let budget := RootContinuation.RootRadialBasisRequest.surfaceBudget basisRequest values
  exact ⟨segment, member, refinement, values, budget, RootContinuation.RootRadialBasisRequest.surfaceBudget_total
    basisRequest values⟩

/-- Prepare energy entries for the supplied original fan segments in order. -/
@[expose] def buildMany (path : List (Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths.Segment regular model sample
  target floor stage))
    (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box)
    {bounds : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds.RegularBasisBounds polynomials
      RootContinuation.RootRadialGeometry.domain}
    (basisRequest : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest.RegularBasisRequest bounds number
      energyTarget energyFloor)
    (geometry : Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisEnergy.AreaRequest.Evaluation.BasisFanGeometry path)
    (parameters : Path.Dyadic.RadialTriangles.Parameters basisRequest.depth) :
    (segments : List (Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths.Segment regular model sample target floor stage))
      →
    (∀ segment ∈ segments, segment ∈ path) → List
      (Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisEnergy.AreaRequest.Evaluation.ArcBasisEnergy (basisRequest :=
      basisRequest) path parameters)
  | [], _ => []
  | segment :: segments, within =>
      Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisEnergy.AreaRequest.Evaluation.ArcBasisEnergy.build path polynomials
        basisRequest geometry parameters segment (within segment List.mem_cons_self) ::

          buildMany
          path polynomials basisRequest geometry parameters segments
          (fun other member => within other (List.mem_cons_of_mem segment member))

/-- The energy entries retain exactly the supplied original segment list. -/
theorem buildMany_segments (path : List (Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths.Segment regular model sample
  target floor stage))
    (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box)
    {bounds : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds.RegularBasisBounds polynomials
      RootContinuation.RootRadialGeometry.domain}
    (basisRequest : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest.RegularBasisRequest bounds number
      energyTarget energyFloor)
    (geometry : Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisEnergy.AreaRequest.Evaluation.BasisFanGeometry path)
    (parameters : Path.Dyadic.RadialTriangles.Parameters basisRequest.depth) :
    (segments : List (Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths.Segment regular model sample target floor stage))
      →
    (within : ∀ segment ∈ segments, segment ∈ path) →
    (Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisEnergy.AreaRequest.Evaluation.ArcBasisEnergy.buildMany path
      polynomials basisRequest geometry parameters segments within).map
      Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisEnergy.AreaRequest.Evaluation.ArcBasisEnergy.segment = segments
  | [], _ => rfl
  | segment :: segments, within => by
      change segment :: _ = segment :: segments
      exact congrArg (List.cons segment)

          (buildMany_segments
          path polynomials basisRequest geometry parameters segments
          (fun other member => within other (List.mem_cons_of_mem segment member)))

/-- The total retained budget is the original segment count times the fixed local budget. -/
theorem budget_sum (entries : List
  (Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisEnergy.AreaRequest.Evaluation.ArcBasisEnergy (basisRequest :=
  basisRequest) path parameters)) :
    FiniteSum.Rational.Squares.coordinateSum (entries.map (fun entry => entry.budget.total)) =
      (entries.length : Normalization.InverseRootPolynomial.Coordinate) * (128 * (2 * bounds.coefficient + 3) *
        basisRequest.tolerance.epsilon) := by
  induction entries with
  | nil => change 0 = 0 * _; ring1
  | cons head tail ih =>
      change head.budget.total + FiniteSum.Rational.Squares.coordinateSum (tail.map (fun entry => entry.budget.total)) =
        _
      rw [head.budget_total, ih, List.length_cons, Nat.cast_succ]
      ring1

/-- The retained budget controls the actual finite boundary energy homogeneously in the coefficient norm. -/
theorem sum_lower (entries : List
  (Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisEnergy.AreaRequest.Evaluation.ArcBasisEnergy (basisRequest :=
  basisRequest) path parameters))
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    -(Readings.PreparedObservationCoercivity.coefficientNormSq coefficients * FiniteSum.Rational.Squares.coordinateSum
      (entries.map (fun entry => entry.budget.total))) ≤
      (Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry => (entry.budget.sample
        coefficients).boundaryArea))).im / 4 := by
  induction entries with
  | nil =>
    change -(Readings.PreparedObservationCoercivity.coefficientNormSq coefficients * 0) ≤ 0 / 4; rw
      [Fraction.Field.mul_zero_direct]; decide
  | cons head tail ih =>
      have bound := Fraction.Order.Arithmetic.add_le_add_direct (head.values.lower head.budget coefficients) ih
      change -(Readings.PreparedObservationCoercivity.coefficientNormSq coefficients * (head.budget.total +
        FiniteSum.Rational.Squares.coordinateSum (tail.map (fun entry => entry.budget.total)))) ≤
        ((head.budget.sample coefficients).boundaryArea + Data.Gaussian.Norm.Sum.Basic.gaussianSum (tail.map (fun entry
          => (entry.budget.sample coefficients).boundaryArea))).im / 4
      rw [Gaussian.Basic.add_im]
      exact (by ring1 : -(Readings.PreparedObservationCoercivity.coefficientNormSq coefficients * (head.budget.total +
        FiniteSum.Rational.Squares.coordinateSum (tail.map (fun entry => entry.budget.total)))) =
        -(Readings.PreparedObservationCoercivity.coefficientNormSq coefficients * head.budget.total) +
          -(Readings.PreparedObservationCoercivity.coefficientNormSq coefficients *
            FiniteSum.Rational.Squares.coordinateSum (tail.map (fun entry => entry.budget.total)))).trans_le
        (bound.trans_eq (by simp only [Fraction.Field.div_eq_mul_inv_direct]; ring1))

/-- The actual fan boundary sum telescopes to its original reversed arc sum and two endpoint radial terms. -/
theorem boundary_sum (entries : List
  (Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisEnergy.AreaRequest.Evaluation.ArcBasisEnergy (basisRequest :=
  basisRequest) path parameters))
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) {first last :
      Normalization.InverseRootPolynomial.Gaussian}
    (chain : Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths.Segment.From first (entries.map
      Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisEnergy.AreaRequest.Evaluation.ArcBasisEnergy.segment) last) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry => (entry.budget.sample
      coefficients).boundaryArea)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry => RootContinuation.RootRadialGeometry.arcArea
        (polynomials.value coefficients) basisRequest.depth
        entry.segment.last.root.coordinate entry.segment.first.root.coordinate)) +
      RootContinuation.RootRadialGeometry.radialArea (polynomials.value coefficients) basisRequest.depth last -
      RootContinuation.RootRadialGeometry.radialArea (polynomials.value coefficients) basisRequest.depth first := by
  induction entries generalizing first with
  | nil => change first = last at chain; rw [chain]; change 0 = 0 + _ - _; ring1
  | cons head tail ih =>
      change first = head.segment.first.root.coordinate ∧ Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths.Segment.From
        head.segment.last.root.coordinate (tail.map
        segment) last at chain
      change (head.budget.sample coefficients).boundaryArea + Data.Gaussian.Norm.Sum.Basic.gaussianSum (tail.map (fun
        entry => (entry.budget.sample coefficients).boundaryArea)) =
        (RootContinuation.RootRadialGeometry.arcArea (polynomials.value coefficients) basisRequest.depth
          head.segment.last.root.coordinate head.segment.first.root.coordinate +
          Data.Gaussian.Norm.Sum.Basic.gaussianSum (tail.map (fun entry => RootContinuation.RootRadialGeometry.arcArea
            (polynomials.value coefficients) basisRequest.depth
            entry.segment.last.root.coordinate entry.segment.first.root.coordinate))) + _ - _
      rw [head.values.boundary_eq_arcs head.budget coefficients, ih chain.2, chain.1]
      ring1

end ArcBasisEnergy
end AreaRequest.Evaluation
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisEnergy
