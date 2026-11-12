module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Energy.AffineTriangle
import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.ReciprocalDiskCoordinateOrientation
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartRefinementArea
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisArcs
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcCoarsening
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinatePolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

@[expose] public section

/-! The whole-cell evaluation supplies geometry to the common segment-based
fan builder; no separate energy implementation is retained. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisGeometry

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartRefinementArea.AreaRequest.Evaluation (square_inside)

variable {genus count : Nat} {curve : Basic.HyperellipticCurve genus} {differential :
  Differentials.Basic.Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {edge : Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    UniformReciprocalCover.Cell data edge}
  {regular : RegularBounds.Data cap} {owners :
    ParentOwners.OwnedEndpoints regular cell}
  {comparison : ArcSamples.Data regular cell} {target :
    Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}
  {index depth stage minimum : Nat} {box : Rational.Box}
  {capSample : Cap.Primitives.Sample cap differential index box}
  {source : UniformReciprocalPrimitives.SourcePrimitive data index}
  {request : ChartAreaRequest.AreaRequest comparison owners target floor}
  {charts : VertexTree.ChartMesh request.mesh capSample minimum}
  {original : ParentCells.ComparedCell comparison source capSample depth}

namespace AreaRequest.Evaluation

variable {evaluated : ChartAreaRequest.AreaRequest.Evaluation charts original
  stage}
  {polynomials : Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}
    {energyTarget : Normalization.InverseRootPolynomial.Coordinate} {energyFloor : Nat}

/-- The actual evaluated odd-degree root-chart path has bounded endpoints and nonnegative fan orientation inherited from
its original parent. -/
theorem basisFanGeometry (evaluated : ChartAreaRequest.AreaRequest.Evaluation
  charts original stage)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (oriented : 0 < Energy.AffineTriangle.crossEnergy (parent.edge.point 0) (parent.edge.point 1)) :
    ChartBasisEnergy.AreaRequest.Evaluation.BasisFanGeometry
      evaluated.vertices.path.segments := open Purelib.Data in open Purelib.Polynomial in by
  have bounded {parameter : Normalization.InverseRootPolynomial.Coordinate}
      (reading : VertexRequests.Reading regular owners.model original.sample
        parameter request.tolerance floor stage) : Data.Gaussian.Norm.Basic.normSq reading.root.coordinate ≤ 2 := by
    have square := reading.square
    rw [branch, pow_one] at square
    have unit := Dense.Gaussian.Reciprocal.Bounds.disk_unit_bound
      (ReciprocalExteriorCollar.inverse_inDisk curve
      (data.boundary.point ⟨edge.left.inside.1.trans reading.prepared.inside.1,
        reading.prepared.inside.2.trans edge.right.inside.2⟩))
    rw [Gaussian.Norm.Basic.normSq_eq_canonical] at unit square
    have scalar := Normalization.ReciprocalDiskCoordinateOrientation.coordinate_norm_upper unit request.small square
    rw [← Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
    exact scalar
  intro segment member
  exact ⟨bounded segment.last, bounded segment.first, (evaluated.coordinate_area_positive branch oriented segment
    member).le⟩

/-- The actual evaluated odd-degree root-chart path retains padded-square containment and the original paid
coordinate-step bound. -/
theorem basisArcGeometry (evaluated : ChartAreaRequest.AreaRequest.Evaluation
  charts original stage)
    (branch : HyperellipticReciprocal.originOrder curve = 1) :
    ChartBasisArcs.Path.BasisArcGeometry
      evaluated.vertices.path request.coordinateBounds.slope := open Purelib.Approximation in by
  intro segment member
  refine ⟨square_inside request branch segment.last,
    square_inside request branch
    segment.first, ?_⟩
  have actual := (evaluated.coordinate_step_bound branch segment member).le
  rw [request.coordinateStep_eq] at actual
  have reading := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct request.mesh_paid (by
      decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 4)
  exact actual.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct le_rfl reading) (by decide)).trans_eq
    (by simp only [Rational.Geometric.Basic.quarterRadius, Fraction.Field.div_eq_mul_inv_direct]; ring1))

end AreaRequest.Evaluation
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisGeometry
