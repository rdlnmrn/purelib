module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.WeightedPeriods
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalPhysicalBoundary
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HolePhysicalCorrection
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Riemann

public section

/-! The existing cached hole requests pay their actual integer-weighted
sum on the canonical cochain used by the standard A/B comparison. The
proof consumes the retained paired source banks and their certified floors. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalHoleCorrection

open Purelib.Topology.Polygon.Stokes

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {differential : Hyperelliptic.Differentials.Basic.Differential genus} {weights : Data.Vector Int
    base.faces.holes.length}
  {prepared : Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts.BoundaryContactPreparations lifted.cutPolygon.patch
    lifted.cutBoundaryPairs differential domains}
  {coefficients : Periods.WeightedPeriods.Coefficients weights} {target : Fraction.Rational} {floor : Nat}

/-- One quarter of a positive rational value is at most that value. -/
private theorem quarter_le {value : Fraction.Rational} (positive : 0 < value) : value / 4 ≤ value := by
  have nonnegative := (Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 4)).le
  have bound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (by decide : (1 : Fraction.Rational) ≤ 4)
    nonnegative
  exact (mul_one (value / 4)).symm.trans_le
    (bound.trans_eq (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))

/-- No sewn-value equality is assumed: physical source uniqueness identifies
the canonical readings with the sources already used by each paired request. -/
theorem canonical_accurate (request : Hyperelliptic.Meshes.PuncturedGrid.HolePhysicalCorrection.HolePhysicalRequest
  prepared coefficients target floor)
    {index : Nat} (later : request.index ≤ index)
    {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains}
      (triangles : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh) :
    Data.Gaussian.Norm.Basic.normSq (coefficients.combine (fun hole : Fin base.faces.holes.length =>
      Topology.Surface.Sewing.SewingRetraction.wordValue
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh triangles.values)
        (base.faces.holes[hole.val].liftedBoundary lifted.vertices lifted.edges))) < target := by
  have bounded (hole : Fin base.faces.holes.length) :
      Gaussian.Basic.Canonical.normSq (Topology.Surface.Sewing.SewingRetraction.wordValue
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh triangles.values)
        ((base.faces.holes[hole.val]'hole.isLt).liftedBoundary lifted.vertices lifted.edges)) ≤ request.perHole := by
    have scalar := Hyperelliptic.Meshes.PuncturedGrid.CanonicalPhysicalBoundary.canonical_hole_accurate
      (base.faces.holes[hole.val]'hole.isLt) (List.getElem_mem hole.isLt)
      (request.rows.get hole).paired triangles
      ((request.rows.get hole).paired_later (request.row_later hole later))
    rw [Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
    exact scalar.le.trans (Hyperelliptic.Meshes.PuncturedGrid.CanonicalHoleCorrection.quarter_le
      request.perHole_positive)
  have bound := coefficients.normSq_combine_le _ (fun _ => request.perHole) bounded
  rw [Gaussian.Norm.Basic.normSq_eq_canonical]
  exact bound.trans_lt ((coefficients.charge_constant request.perHole).trans_lt request.paid)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalHoleCorrection
