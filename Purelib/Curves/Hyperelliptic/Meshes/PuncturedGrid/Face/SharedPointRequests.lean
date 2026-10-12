module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.RequestedFragments
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SharedPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveRequestWeakening
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh
import Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularExteriorBoundary
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Data.Rat

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.RectangularPointReadings

@[expose] public section

/-! Actual contained-path integrals compared with arbitrary retained point
banks on the supplied face primitives, including subdivided boundary points. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SharedPointRequests

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths (EnteredPath)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    RegularFace bank} {models :
    FaceModels frames face}
  {base finish : Purelib.Data.Gaussian.Basic.Canonical} {owner :
    Owner (curve.polynomial.eval base)} {ambient :
    Purelib.Geometry.Rational.Box}
  {path : Polynomial.Geometry.ClearPath curve.polynomial ambient base finish} {prepared :
    CoveredTracedPath path owner}
  {differential : Differential genus} {parentSheet : Fin 2}

/-- The exact shared primitive caches bound endpoint-owner changes between the retained arbitrary point bank and the
original path readings. -/
theorem point_increment_bound (entered : EnteredPaths.EnteredPath models prepared differential parentSheet) {target :
  InverseRootPolynomial.Coordinate}
    (request : RequestedFragments entered.mesh entered.bounds entered.globalBounds genus target)
    {index : Nat} (data : PrimitiveData.DomainPrimitives entered.domain differential index) (shared : entered.UsesData
      request data)
    {count : Nat} {points : Fin count → Data.Gaussian.Basic.Canonical}
    (readings : RectangularPointReadings.PointReadings data.anchors data.offsets points)
    (first last : Fin count) (firstEq : points first = base) (lastEq : points last = finish) :
    Data.Gaussian.Norm.Basic.normSq ((readings.values last - readings.values first) -
      (request.readings.values entered.last - request.readings.values entered.first)) ≤ 16 *
        request.budget.grid.globalBound := by
  rcases data with ⟨primitives, anchors, offsets, corners⟩
  rcases shared with ⟨indexEq, primitivesEq, anchorsEq, offsetsEq⟩
  cases indexEq
  cases eq_of_heq primitivesEq
  cases eq_of_heq anchorsEq
  cases eq_of_heq offsetsEq
  have scalar := GridPrimitiveAccuracy.point_increment_bound
    request.budget.grid readings request.readings entered.domain.patch.cell_refines
    first last entered.first entered.last (entered.first_eq.trans firstEq.symm) (entered.last_eq.trans lastEq.symm)
  simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using scalar

/-- The fragment budget already leaves sufficient room to normalize both endpoints. This bound pays every fragment and
remains valid for empty paths. -/
theorem point_accurate (entered : EnteredPaths.EnteredPath models prepared differential parentSheet) {target :
  InverseRootPolynomial.Coordinate}
    (request : RequestedFragments entered.mesh entered.bounds entered.globalBounds genus target)
    {index : Nat} (data : PrimitiveData.DomainPrimitives entered.domain differential index) (shared : entered.UsesData
      request data)
    {count : Nat} {points : Fin count → Data.Gaussian.Basic.Canonical}
    (readings : RectangularPointReadings.PointReadings data.anchors data.offsets points)
    (first last : Fin count) (firstEq : points first = base) (lastEq : points last = finish) :
    Data.Gaussian.Norm.Basic.normSq ((readings.values last - readings.values first) -
      request.request.primitiveSum) < target := by
  have ownerBound := point_increment_bound
    entered request data shared readings first last firstEq lastEq
  have analytic := entered.accurate request
  have perLe : request.budget.perFragment ≤ target / 4 := by
    rw [request.budget.perFragment_eq]
    exact Aggregate.perTerm_le request.budget.target_positive.le _
  have ownership : 32 * request.budget.grid.globalBound < target / 4 :=
    request.budget.ownership_accurate.trans_le
      ((Fraction.Order.Field.divide_le_self request.budget.perFragment_positive.le (by decide)).trans perLe)
  have identity : (readings.values last - readings.values first) - request.request.primitiveSum =
      ((readings.values last - readings.values first) - (request.readings.values entered.last - request.readings.values
        entered.first)) +
        ((request.readings.values entered.last - request.readings.values entered.first) - request.request.primitiveSum)
          := by ring1
  rw [identity]
  have triangle := Data.Gaussian.Norm.Bounds.normSq_add_le_two
    ((readings.values last - readings.values first) - (request.readings.values entered.last - request.readings.values
      entered.first))
    ((request.readings.values entered.last - request.readings.values entered.first) - request.request.primitiveSum)
  simp only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at triangle ownerBound analytic
  rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
  have estimate := triangle.trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add ownerBound analytic.le) (by
        decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2))
  have total : 2 * (16 * request.budget.grid.globalBound + target / 4) < target := by
    have paid := Fraction.Order.Arithmetic.add_lt_add_right_direct ownership (target / 4)
    have quarter : target / 4 + target / 4 + target / 4 + target / 4 = target := by
      rw [show target / 4 + target / 4 + target / 4 + target / 4 = (target / 4) * 4 by ring1]
      exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
    have paid' := Fraction.Order.Arithmetic.add_lt_add_right_direct paid (target / 4)
    have remaining := Fraction.Order.Arithmetic.add_lt_add_left_direct request.budget.target_positive
      (target / 4 + target / 4 + target / 4)
    have final := paid'.trans (by simpa only [add_zero] using remaining)
    exact (show 2 * (16 * request.budget.grid.globalBound + target / 4) =
      32 * request.budget.grid.globalBound + target / 4 + target / 4 by ring1).trans_lt (final.trans_eq quarter)
  exact estimate.trans_lt total

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SharedPointRequests
