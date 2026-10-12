module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SharedCornerRequests
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.RootContinuation.RootOwnerFrames

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners

open Purelib.Data.Rat

open Purelib.Integration.Polynomial.Rectangle.Accuracy

open Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests

@[expose] public section

/-!
# Fixed finite references for all later face primitives

A coarse prepared request is materialized once, before choosing a final
face index. Every later face bank is compared with that same cached sum.
The resulting increment bound does not grow with the refinement index.
Generated requests may be supplied directly, with exact semantic readbacks;
neither the preparation nor its numerical sum must equal a fallback search.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners.FaceCorners (point inside)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths (EnteredPath)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment (FragmentAccuracy)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledSumRequest)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)

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

set_option genInjectivity false in
/-- The reference is independent of the later numerical face bank. In particular, its value and bound are executable
cached data, not repeated evaluations hidden inside an inequality. -/
structure Reference (entered : EnteredPaths.EnteredPath models prepared differential parentSheet) (target :
  InverseRootPolynomial.Coordinate) where
  /-- The original reference accuracy target is positive. -/ positive : 0 < target
  /-- The retained scalar fragment budget on the original entered face path. -/ budget : Fragment.FragmentAccuracy
    entered.globalBounds entered.domain.steps entered.mesh.splits.pieceCount (target / 4)
  /-- The cached original prepared-parent integration request. -/ request :
    PreparedControlledPrimitiveRequests.ControlledSumRequest entered.cache.parents genus (target / 4)
  /-- The cached request meets the retained fragment budget's exact parent-stage floor. -/ minimum : budget.minimumIndex
    ≤ request.minimumIndex
  /-- The cached actual primitive sum of the retained original request. -/ value : Data.Gaussian.Basic.Canonical
  /-- The reference value reads back that exact prepared primitive sum. -/ value_eq : value = request.primitiveSum
  /-- The cached stage-independent squared-norm bound for all later retained face increments. -/ bound :
    InverseRootPolynomial.Coordinate
  /-- The bound is twice the original target plus squared norm of the exact cached reference value. -/ bound_eq : bound
    = 2 * (target + Data.Gaussian.Norm.Basic.normSq value)

constructive_injectivity Reference

namespace Reference

variable {entered : EnteredPath models prepared
  differential parentSheet} {target : Coordinate}

/-- Retain the supplied checked parent request and materialize its exact reference sum and finite bound once. -/
def ofRequest (budget : Fragment.FragmentAccuracy entered.globalBounds entered.domain.steps
  entered.mesh.splits.pieceCount (target / 4))
    (request : PreparedControlledPrimitiveRequests.ControlledSumRequest entered.cache.parents genus (target / 4))
    (minimum : budget.minimumIndex ≤ request.minimumIndex) (positive : 0 < target) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences.Reference entered target :=
  let value := request.primitiveSum
  ⟨positive, budget, request, minimum, value, rfl, 2 * (target + Data.Gaussian.Norm.Basic.normSq value), rfl⟩

/-- A total fallback producer. Subsequent refinements consume the retained request; they do not acquire another
integration or recompute its sum. -/
def build (entered : EnteredPaths.EnteredPath models prepared differential parentSheet) (target :
  InverseRootPolynomial.Coordinate) (positive : 0 < target) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences.Reference entered target :=
  have quarterPositive := Fraction.Order.Field.div_pos_direct positive (by
      decide : (0 : InverseRootPolynomial.Coordinate) < 4)
  let budget := FragmentAccuracy.build entered.globalBounds entered.domain.steps entered.mesh.splits.pieceCount (target
    / 4) quarterPositive
  let request := ControlledSumRequest.acquire entered.cache.covered entered.cache.proper (target / 4) quarterPositive
    budget.minimumIndex
  ofRequest budget request
    (ControlledSumRequest.acquire_minimumIndex ..).symm.le positive

/-- The reference constructed from a supplied parent request retains that exact request. -/
theorem ofRequest_request (budget : Fragment.FragmentAccuracy entered.globalBounds entered.domain.steps
  entered.mesh.splits.pieceCount (target / 4))
    (request : PreparedControlledPrimitiveRequests.ControlledSumRequest entered.cache.parents genus (target / 4))
    (minimum : budget.minimumIndex ≤ request.minimumIndex) (positive : 0 < target) :
    (ofRequest budget request minimum
      positive).request = request := rfl

/-- The retained reference bound is strictly positive. -/
theorem bound_positive (reference : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences.Reference entered
  target) : 0 < reference.bound := by
  rw [reference.bound_eq]
  have translated : Data.Gaussian.Norm.Basic.normSq reference.value < target +
    Data.Gaussian.Norm.Basic.normSq reference.value := by
    simpa only [zero_add] using
      Fraction.Order.Arithmetic.add_lt_add_right_direct reference.positive (Data.Gaussian.Norm.Basic.normSq
        reference.value)
  exact Fraction.Order.Arithmetic.mul_pos_direct (by decide)
    ((Data.Gaussian.Norm.Basic.normSq_nonneg _).trans_lt translated)

/-- Only the face-polynomial index increases. The original parent request and its finite sum remain fixed throughout
this estimate. -/
theorem accurate (reference : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences.Reference entered
  target) {index : Nat} (later : reference.budget.grid.index ≤ index)
    (data : PrimitiveData.DomainPrimitives entered.domain differential index)
    (first last : Fin 4)
    (firstEq : FaceCorners.point face.cell.box first = base)
    (lastEq : FaceCorners.point face.cell.box last = finish) :
    Data.Gaussian.Norm.Basic.normSq ((data.corners.values last - data.corners.values first) - reference.value)
      < target := by
  rw [reference.value_eq]
  exact SharedCornerRequests.corner_accurate entered
    (entered.requestSharedWith reference.budget index later data reference.request reference.minimum)
    data (entered.requestSharedWith_usesData ..) first last firstEq lastEq

/-- Every sufficiently refined actual face-corner increment satisfies the fixed retained reference bound. -/
theorem bounded (reference : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences.Reference entered
  target) {index : Nat} (later : reference.budget.grid.index ≤ index)
    (data : PrimitiveData.DomainPrimitives entered.domain differential index)
    (first last : Fin 4)
    (firstEq : FaceCorners.point face.cell.box first = base)
    (lastEq : FaceCorners.point face.cell.box last = finish) :
    Data.Gaussian.Norm.Basic.normSq (data.corners.values last - data.corners.values first) ≤ reference.bound :=
      by
  have accurate := reference.accurate later data first last firstEq lastEq
  have estimate := (Data.Gaussian.Norm.Bounds.normSq_add_le_two
    ((data.corners.values last - data.corners.values first) - reference.value) reference.value).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add accurate.le le_rfl) (by decide))
  rw [sub_add_cancel, ← reference.bound_eq] at estimate
  exact estimate

end Reference
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences
