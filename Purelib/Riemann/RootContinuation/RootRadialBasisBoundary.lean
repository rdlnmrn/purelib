module
import Purelib.Riemann.Readings.AffineBasisEnergy
public import Purelib.Riemann.RootContinuation.RootRadialBasisEnergy
import Purelib.Riemann.RootContinuation.RootRadialGeometry
import Purelib.Riemann.RootContinuation.RootRadialRefinement
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Energy.Polygon

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest
import Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Riemann.RootContinuation.RootRadialBasisRequest
public import Purelib.Riemann.RootContinuation.RootRadialBoundary
import Purelib.Riemann.Topology.PreparedSurfacePartitions
import Purelib.Riemann.Topology.PrimitiveSurfaceBudget
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation

@[expose] public section

/-! Exact outer-arc and radial readback for a homogeneous root-coordinate
fan. Both endpoint terms remain available to the actual sheet-return proof. -/
namespace Purelib.Riemann.RootContinuation

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Integration.Energy.Polygon (energyPrimitivePoint)
open Purelib.Riemann.Readings.AffineBasisEnergy (AffineBasis)
open Purelib.Topology.Polygon.Stokes (edgeArea edgeListArea)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds (RegularBasisBounds)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest (RegularBasisRequest)
open Purelib.Riemann.Normalization
open Purelib.Riemann.RootContinuation.RootRadialGeometry
open Purelib.Riemann.RootContinuation.RootRadialRefinement (Refinement)
open Purelib.Riemann.RootContinuation.RootRadialBasisEnergy (BasisValues)
open Purelib.Riemann.RootContinuation.RootRadialBasisRequest (surfaceBudget lower)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {index : Nat} {box : Purelib.Geometry.Rational.Box} {first last :
    Purelib.Data.Gaussian.Basic.Canonical} {depth : Nat}
  {parameters : Purelib.Integration.Path.Dyadic.RadialTriangles.Parameters depth} {refinement : Refinement first last
    parameters}
  {polynomials : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap
    index box}

namespace RootRadialBasisEnergy.BasisValues

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rectangle.Partition in
open Purelib.Integration.Energy in
open Purelib.Integration.Path.Dyadic in
open Purelib.LinearAlgebra.Gaussian in
/-- Read the retained radial basis energy boundary on the parameter rectangle.

Uses the sample value identities and refinement coordinates to identify every boundary edge with the same
coefficient-combined polynomial evaluated on the unit box. -/
theorem boundary_eq_rectangle (sample : BasisValues refinement polynomials)
    (budget : AffineBasis.SurfaceBudget sample.basis) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector
      genus) :
    (budget.sample coefficients).boundaryArea = PreparedBoxBoundary.rectangleBoundary
      (fun parameter => Polygon.energyPrimitivePoint (polynomials.value coefficients (point first last parameter)))
      depth RadialTriangles.unitBox := by
  rw [(budget.sample coefficients).boundaryArea_eq]
  change edgeListArea (fun vertex => Polygon.energyPrimitivePoint ((budget.sample coefficients).primitiveValue vertex))
    parameters.mesh.mesh.triangulation.boundary = _
  calc
    _ = edgeListArea (fun vertex => Polygon.energyPrimitivePoint (polynomials.value coefficients
        (point first last (parameters.mesh.mesh.coordinate vertex)))) parameters.mesh.mesh.triangulation.boundary := by
      generalize parameters.mesh.mesh.triangulation.boundary = edges
      induction edges with
      | nil => rfl
      | cons edge edges ih =>
          change edgeArea _ _ + edgeListArea _ edges = edgeArea _ _ + edgeListArea _ edges
          apply congrArg₂ (fun left right : Basic.Canonical => left + right) ?_ ih
          dsimp only
          rw [sample.value_readback budget coefficients, sample.value_readback budget coefficients,
            refinement.coordinates_eq, refinement.coordinates_eq]
    _ = PreparedBoxBoundary.rectangleBoundary
        (fun parameter => Polygon.energyPrimitivePoint (polynomials.value coefficients (point first last parameter)))
        depth parameters.mesh.partition.parent :=
          PreparedBoxBoundary.TriangulatedPartition.boundaryArea_eq_rectangleBoundary parameters.mesh
          (fun parameter => Polygon.energyPrimitivePoint (polynomials.value coefficients (point first last parameter)))
    _ = _ := by rw [parameters.parent_eq]

open Purelib.LinearAlgebra.Gaussian in
/-- Decompose the radial basis boundary into two radii and the connecting arc.

Preserves the first-to-last orientation: the initial radial area is added and the final radial area is subtracted. -/
theorem boundary_eq_arcs (sample : BasisValues refinement polynomials)
    (budget : AffineBasis.SurfaceBudget sample.basis) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector
      genus) :
    (budget.sample coefficients).boundaryArea = radialArea (polynomials.value coefficients) depth first +
      arcArea (polynomials.value coefficients) depth first last - radialArea (polynomials.value coefficients) depth last
        := by
  rw [sample.boundary_eq_rectangle budget coefficients]
  exact rectangle_boundary (polynomials.value coefficients) depth first last

end RootRadialBasisEnergy.BasisValues

namespace RootRadialBasisBoundary.BasisRequest

variable {bounds : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds.RegularBasisBounds
  polynomials RootRadialGeometry.domain}
  {count minimum : Nat} {target : Purelib.Data.Rat.Fraction.Rational} (request :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest.RegularBasisRequest bounds count target
    minimum)
  {parameters : Purelib.Integration.Path.Dyadic.RadialTriangles.Parameters request.depth} {refinement : Refinement first
    last parameters}

open Purelib.LinearAlgebra.Gaussian in
open Purelib.Riemann.Readings in
/-- Lower-bound the oriented radial and arc area for a basis request.

Transports the retained surface budget through the exact arc decomposition, with coefficient norm, tolerance and the
original factor 128 unchanged. -/
theorem arcs_lower (sample : BasisValues refinement polynomials) (coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    -(PreparedObservationCoercivity.coefficientNormSq coefficients *
      (128 * (2 * bounds.coefficient + 3) * request.tolerance.epsilon)) ≤
      (radialArea (polynomials.value coefficients) request.depth first +
        arcArea (polynomials.value coefficients) request.depth first last -
        radialArea (polynomials.value coefficients) request.depth last).im / 4 := by
  have bound := lower request sample coefficients
  rw [sample.boundary_eq_arcs (surfaceBudget request sample) coefficients] at bound
  exact bound

end RootRadialBasisBoundary.BasisRequest
end Purelib.Riemann.RootContinuation
