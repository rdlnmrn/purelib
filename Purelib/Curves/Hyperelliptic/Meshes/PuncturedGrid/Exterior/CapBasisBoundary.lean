module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Energy.Polygon

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapRefinement
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBoundary
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Readings.AffineBasisEnergy
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Riemann.Topology.PreparedSurfacePartitions
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Mesh.CoordinateTriangulation

open Purelib.Curves

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Exact inverse-arc readback for arbitrary coefficient combinations on the regular cap. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy

open Purelib.Topology.Polygon.Stokes

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains differential} {attached :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment prepared}
  {geometry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry
    attached} {coarse : Topology.Polygon.Stokes.OrientedTriangle (lifted.vertices.count + attached.words.length)}
  {depth : Nat} {parameters : Path.Dyadic.RadialTriangles.Parameters depth}
  {index : Nat} {box : Rational.Box}

namespace RegularBasisSample

variable {refinement : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapRefinement.Refinement geometry coarse parameters}
  {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}

/-- The homogeneous energy uses the actual combined polynomial on the
retained radial parameter mesh. -/
theorem boundary_eq_rectangle (sample : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisSample
  refinement polynomials)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    (sample.budget.sample coefficients).boundaryArea = Rectangle.Partition.PreparedBoxBoundary.rectangleBoundary
      (fun point => Energy.Polygon.energyPrimitivePoint (polynomials.value coefficients (geometry.point coarse point.re
        point.im)))
      depth Path.Dyadic.RadialTriangles.unitBox := by
  change Topology.Polygon.Stokes.edgeListArea (fun vertex => Energy.Polygon.energyPrimitivePoint ((sample.budget.sample
    coefficients).primitiveValue vertex))
    parameters.mesh.mesh.triangulation.boundary = _
  calc
    _ = Topology.Polygon.Stokes.edgeListArea (fun vertex => Energy.Polygon.energyPrimitivePoint (polynomials.value
      coefficients (geometry.point coarse
        (parameters.mesh.mesh.coordinate vertex).re (parameters.mesh.mesh.coordinate vertex).im)))
        parameters.mesh.mesh.triangulation.boundary := by
      generalize parameters.mesh.mesh.triangulation.boundary = edges
      induction edges with
      | nil => rfl
      | cons edge edges ih =>
          simp only [Topology.Polygon.Stokes.edgeListArea]
          rw [ih, sample.value_readback, sample.value_readback, refinement.coordinates_eq, refinement.coordinates_eq]
    _ = Rectangle.Partition.PreparedBoxBoundary.rectangleBoundary
        (fun point => Energy.Polygon.energyPrimitivePoint (polynomials.value coefficients (geometry.point coarse
          point.re point.im)))
        depth parameters.mesh.partition.parent :=
          Rectangle.Partition.PreparedBoxBoundary.TriangulatedPartition.boundaryArea_eq_rectangleBoundary
          parameters.mesh
          (fun point => Energy.Polygon.energyPrimitivePoint (polynomials.value coefficients (geometry.point coarse
            point.re point.im)))
    _ = _ := by rw [parameters.parent_eq]

/-- The complete conjugate energy boundary contains the inverse source arc
and both radial sides, before cancellation across the attachment fan. -/
theorem boundary_eq_arc (sample : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisSample
  refinement polynomials)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    (sample.budget.sample coefficients).boundaryArea =
      Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.radialArea (polynomials.value coefficients) depth
        (geometry.sourceCoordinates coarse.second) +
      Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.arcArea (polynomials.value coefficients) depth
        (geometry.sourceCoordinates coarse.second) (geometry.sourceCoordinates coarse.third) -
      Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.radialArea (polynomials.value coefficients) depth
        (geometry.sourceCoordinates coarse.third) := by
  rw [sample.boundary_eq_rectangle]
  exact Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.rectangle_boundary (polynomials.value coefficients)
    depth _ _

end RegularBasisSample
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
