module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.RequestedFragments
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SharedCornerRequests
public import Purelib.Riemann.Readings.PreparedPrimitiveRequestBatches
import Init.Data.Nat.MinMax
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
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SharedPrimitiveRequests
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
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
import Purelib.Tactic.Ring

section

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners

open Purelib.Data.Rat

open Purelib.Integration.Polynomial.Rectangle.Accuracy

open Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment

open Purelib.Riemann.Integration

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests

open Purelib.Riemann.Readings.PreparedPrimitiveRequestBatches

public section

/-!
# Two face primitives compared through one actual prepared path

The two entries retain the same incoming owner and preparation, but may use
different face domains, sheets, and split meshes. Their scalar floors are
selected before numerical construction. One checked parent request then
compares both face increments with exactly the same primitive sum.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledSumRequest)
open Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment (FragmentAccuracy)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths (EnteredPath)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners.FaceCorners (point)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {firstFace lastFace :
    RegularFace bank}
  {firstModels : FaceModels frames
    firstFace} {lastModels :
    FaceModels frames lastFace}
  {start finish : Purelib.Data.Gaussian.Basic.Canonical} {owner :
    Owner (curve.polynomial.eval start)} {ambient :
    Purelib.Geometry.Rational.Box}
  {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish} {prepared :
    CoveredTracedPath path owner}
  {differential : Differential genus} {parentSheet : Fin 2}
  (first : EnteredPath firstModels prepared
    differential parentSheet)
  (last : EnteredPath lastModels prepared
    differential parentSheet)

set_option genInjectivity false in
/-- A cached tolerance and common lower indices for two retained face comparisons.

The two face budgets retain separate prepared-request floors. Their maxima
select the shared parent floor and face-model index before numerical construction. -/
structure ContactBudget (target : InverseRootPolynomial.Coordinate) where
  /-- The cached common local tolerance shared by both retained face comparisons. -/ tolerance :
    InverseRootPolynomial.Coordinate
  /-- The common local tolerance is exactly one quarter of the original contact target. -/ tolerance_eq : tolerance =
    target / 4
  /-- The retained common local tolerance is positive. -/ tolerance_positive : 0 < tolerance
  /-- The first face's retained scalar accuracy budget or actual requested fragment bank. -/ left :
    Fragment.FragmentAccuracy first.globalBounds first.domain.steps first.mesh.splits.pieceCount (tolerance / 4)
  /-- The second face's retained scalar accuracy budget or actual requested fragment bank. -/ right :
    Fragment.FragmentAccuracy last.globalBounds last.domain.steps last.mesh.splits.pieceCount (tolerance / 4)
  /-- The cached common floor for the actual prepared-parent request. -/ minimum : Nat
  /-- The parent floor is the maximum of both original face-budget floors. -/ minimum_eq : minimum = max
    left.minimumIndex right.minimumIndex
  /-- The cached common face-model index selected before numerical construction. -/ index : Nat
  /-- The common face index is the maximum of both retained grid request indices. -/ index_eq : index = max
    left.grid.index right.grid.index

constructive_injectivity ContactBudget

namespace ContactBudget

/-- Allocate the original contact target between the two retained face budgets and cache both common lower indices. -/
@[expose] def build (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests.ContactBudget first last target :=
  let tolerance := target / 4
  have tolerancePositive := Fraction.Order.Field.div_pos_direct positive (by
      decide : (0 : InverseRootPolynomial.Coordinate) < 4)
  have quarterPositive := Fraction.Order.Field.div_pos_direct tolerancePositive (by
      decide : (0 : InverseRootPolynomial.Coordinate) < 4)
  let left := FragmentAccuracy.build first.globalBounds first.domain.steps first.mesh.splits.pieceCount (tolerance / 4)
    quarterPositive
  let right := FragmentAccuracy.build last.globalBounds last.domain.steps last.mesh.splits.pieceCount (tolerance / 4)
    quarterPositive
  ⟨tolerance, rfl, tolerancePositive, left, right, max left.minimumIndex right.minimumIndex, rfl,
    max left.grid.index right.grid.index, rfl⟩

variable {first last} {target : Coordinate}

/-- Any index above the retained common face index is sufficient for the first face's grid request. -/
theorem left_later (budget : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests.ContactBudget first last
  target) {index : Nat} (later : budget.index ≤ index) :
    budget.left.grid.index ≤ index := by
  rw [budget.index_eq] at later
  exact (Data.Nat.Order.le_max_left _ _).trans later

/-- Any index above the retained common face index is sufficient for the second face's grid request. -/
theorem right_later (budget : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests.ContactBudget first last
  target) {index : Nat} (later : budget.index ≤ index) :
    budget.right.grid.index ≤ index := by
  rw [budget.index_eq] at later
  exact (Data.Nat.Order.le_max_right _ _).trans later

set_option genInjectivity false in
/-- Two retained face comparisons sharing one actual prepared primitive sum.

Each comparison keeps its supplied primitive data and actual request. The
retained sum equality identifies the exact cached sums used on both faces. -/
structure Comparison (budget : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests.ContactBudget first last
  target) {index : Nat}
    (leftData : PrimitiveData.DomainPrimitives first.domain differential index) (rightData :
      PrimitiveData.DomainPrimitives last.domain differential index) where
  /-- The first face's retained scalar accuracy budget or actual requested fragment bank. -/ left :
    RequestedFragments first.mesh first.bounds first.globalBounds genus budget.tolerance
  /-- The second face's retained scalar accuracy budget or actual requested fragment bank. -/ right :
    RequestedFragments last.mesh last.bounds last.globalBounds genus budget.tolerance
  /-- The first actual comparison uses exactly the supplied first-face primitive caches. -/ left_data : first.UsesData
    left leftData
  /-- The second actual comparison uses exactly the supplied second-face primitive caches. -/ right_data : last.UsesData
    right rightData
  /-- Both retained comparisons consume the same actual prepared primitive sum. -/ sum_eq : left.request.primitiveSum =
    right.request.primitiveSum

constructive_injectivity Comparison

/-- A generated checked parent request is reused literally on both faces. Changing the parent-list index is erased
transport, not another preparation. -/
@[expose] def compareWith (budget : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests.ContactBudget first
  last target) {index : Nat} (later : budget.index ≤ index)
    (leftData : PrimitiveData.DomainPrimitives first.domain differential index) (rightData :
      PrimitiveData.DomainPrimitives last.domain differential index)
    (request : PreparedControlledPrimitiveRequests.ControlledSumRequest first.cache.parents genus (budget.tolerance /
      4)) (minimum : budget.minimum ≤ request.minimumIndex) :
    Comparison budget leftData rightData :=
  have leftMinimum : budget.left.minimumIndex ≤ request.minimumIndex :=
    (Data.Nat.Order.le_max_left _ _).trans ((budget.minimum_eq ▸ minimum) : max budget.left.minimumIndex
      budget.right.minimumIndex ≤ request.minimumIndex)
  have rightMinimum : budget.right.minimumIndex ≤ request.minimumIndex :=
    (Data.Nat.Order.le_max_right _ _).trans ((budget.minimum_eq ▸ minimum) : max budget.left.minimumIndex
      budget.right.minimumIndex ≤ request.minimumIndex)
  let equal := first.cache.parents_eq.trans last.cache.parents_eq.symm
  let rightRequest := ControlledSumRequest.castParents request equal
  have rightLater : budget.right.minimumIndex ≤ rightRequest.minimumIndex :=
    (ControlledSumRequest.castParents_minimumIndex request equal).symm ▸ rightMinimum
  let left := first.requestSharedWith budget.left index (budget.left_later later) leftData request leftMinimum
  let right := last.requestSharedWith budget.right index (budget.right_later later) rightData rightRequest rightLater
  ⟨left, right, first.requestSharedWith_usesData .., last.requestSharedWith_usesData ..,
    (ControlledSumRequest.castParents_primitiveSum request equal).symm⟩

/-- Acquire one common prepared-parent request and reuse it on both supplied retained face caches. -/
@[expose] def compare (budget : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests.ContactBudget first last
  target) {index : Nat} (later : budget.index ≤ index)
    (leftData : PrimitiveData.DomainPrimitives first.domain differential index) (rightData :
      PrimitiveData.DomainPrimitives last.domain differential index) :
    Comparison budget leftData rightData :=
  let request := ControlledSumRequest.acquire first.cache.covered first.cache.proper (budget.tolerance / 4)
    budget.left.target_positive budget.minimum
  budget.compareWith later leftData rightData request (ControlledSumRequest.acquire_minimumIndex ..).symm.le

/-- The first face comparison retains the supplied prepared-parent request exactly. -/
theorem compareWith_left_request (budget : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests.ContactBudget
  first last target) {index : Nat} (later : budget.index ≤ index)
    (leftData : PrimitiveData.DomainPrimitives first.domain differential index) (rightData :
      PrimitiveData.DomainPrimitives last.domain differential index)
    (request : PreparedControlledPrimitiveRequests.ControlledSumRequest first.cache.parents genus (budget.tolerance /
      4)) (minimum : budget.minimum ≤ request.minimumIndex) :
    (budget.compareWith later leftData rightData request minimum).left.request = request := rfl

/-- The second face comparison retains the supplied prepared-parent request up to erased parent-list transport. -/
theorem compareWith_right_request (budget : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests.ContactBudget
  first last target) {index : Nat} (later : budget.index ≤ index)
    (leftData : PrimitiveData.DomainPrimitives first.domain differential index) (rightData :
      PrimitiveData.DomainPrimitives last.domain differential index)
    (request : PreparedControlledPrimitiveRequests.ControlledSumRequest first.cache.parents genus (budget.tolerance /
      4)) (minimum : budget.minimum ≤ request.minimumIndex) :
    HEq (budget.compareWith later leftData rightData request minimum).right.request request :=
      ControlledSumRequest.castParents_heq request _

namespace Comparison

variable {budget : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests.ContactBudget first last
  target} {index : Nat}
  {leftData : DomainPrimitives first.domain
    differential index} {rightData :
    DomainPrimitives last.domain differential
    index}

/-- Sheet agreement comes from the common actual incoming owner retained by the two entries. Reversal of the second
face's boundary is explicit in the difference of the two forward increments. -/
theorem accurate (comparison : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests.ContactBudget.Comparison
  budget leftData rightData)
    (leftStart leftFinish rightStart rightFinish : Fin 4)
    (leftStart_eq : FaceCorners.point firstFace.cell.box leftStart = start)
    (leftFinish_eq : FaceCorners.point firstFace.cell.box leftFinish = finish)
    (rightStart_eq : FaceCorners.point lastFace.cell.box rightStart = start)
    (rightFinish_eq : FaceCorners.point lastFace.cell.box rightFinish = finish) :
    Data.Gaussian.Norm.Basic.normSq ((leftData.corners.values leftFinish - leftData.corners.values leftStart) -
      (rightData.corners.values rightFinish - rightData.corners.values rightStart)) < target := by
  have left := SharedCornerRequests.corner_accurate first comparison.left leftData comparison.left_data leftStart
    leftFinish leftStart_eq leftFinish_eq
  have right := SharedCornerRequests.corner_accurate last comparison.right rightData comparison.right_data rightStart
    rightFinish rightStart_eq rightFinish_eq
  rw [← comparison.sum_eq] at right
  have equal : (leftData.corners.values leftFinish - leftData.corners.values leftStart) -
      (rightData.corners.values rightFinish - rightData.corners.values rightStart) =
      ((leftData.corners.values leftFinish - leftData.corners.values leftStart) - comparison.left.request.primitiveSum)
        -
        ((rightData.corners.values rightFinish - rightData.corners.values rightStart) -
          comparison.left.request.primitiveSum) := by ring1
  rw [equal]
  apply (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans_lt
  have paid := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
      decide : (0 : InverseRootPolynomial.Coordinate) < 2)
    (Fraction.Order.Arithmetic.add_lt_add_direct left right)
  apply paid.trans_eq
  rw [budget.tolerance_eq, show 2 * (target / 4 + target / 4) = (target / 4) * 4 by ring1]
  exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)

end Comparison

/-- Only the corner data survive execution of a contact bound: the common prepared request used to prove the estimate is
proof-local and is erased. -/
theorem accurate (budget : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests.ContactBudget first last
  target) {index : Nat} (later : budget.index ≤ index)
    (leftData : PrimitiveData.DomainPrimitives first.domain differential index) (rightData :
      PrimitiveData.DomainPrimitives last.domain differential index)
    (leftStart leftFinish rightStart rightFinish : Fin 4)
    (leftStart_eq : FaceCorners.point firstFace.cell.box leftStart = start)
    (leftFinish_eq : FaceCorners.point firstFace.cell.box leftFinish = finish)
    (rightStart_eq : FaceCorners.point lastFace.cell.box rightStart = start)
    (rightFinish_eq : FaceCorners.point lastFace.cell.box rightFinish = finish) :
    Data.Gaussian.Norm.Basic.normSq ((leftData.corners.values leftFinish - leftData.corners.values leftStart) -
      (rightData.corners.values rightFinish - rightData.corners.values rightStart)) < target :=
  (budget.compare later leftData rightData).accurate leftStart leftFinish rightStart rightFinish
    leftStart_eq leftFinish_eq rightStart_eq rightFinish_eq

end ContactBudget
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests

end
