module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths.Polynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Tactic.Ring

/-! # One genuine full-polynomial common bank for two original face entries

The original entries retain the same covered path and root owners. The two
P-specific bounds and scalar budget precede all numerical reads. One actual
PolynomialWork/Models bank then supplies the SAME common integral to both
face comparisons, with joint parent-list transport on the second face.
The legacy ControlledSumRequest comparison remains a distinct unchanged API.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests.ContactBudget

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents (PolynomialWork)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths (EnteredPath)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
    {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
    {frames : RootFrames bank.grid} {firstFace lastFace : RegularFace bank}
    {firstModels : FaceModels frames firstFace} {lastModels : FaceModels frames lastFace}
    {start finish : Canonical} {owner : Owner (curve.polynomial.eval start)} {ambient : Geometry.Rational.Box}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {prepared : CoveredTracedPath path owner} {basis : Differential genus} {parentSheet : Fin 2}
    (first : EnteredPath firstModels prepared basis parentSheet)
    (last : EnteredPath lastModels prepared basis parentSheet)
    (differential : OddPowerDifferential curve.polynomial)

/-- The two genuine P-bound caches and their original common contact budget, each with its whole factory. -/
@[expose] def PolynomialPreparation (target : Rational) (positive : 0 < target) : Type _ :=
  {_ordinary : Unit // differential.denominatorPairs = 0} ×
  (left : {value : PrimitiveOverlapBounds firstFace.clearance (differential.numerator.scale differential.scale) //
    value = PrimitiveOverlapBounds.build firstFace.clearance (differential.numerator.scale differential.scale)}) ×
  (right : {value : PrimitiveOverlapBounds lastFace.clearance (differential.numerator.scale differential.scale) //
    value = PrimitiveOverlapBounds.build lastFace.clearance (differential.numerator.scale differential.scale)}) ×
  {budget : ContactBudget first last target
      (bounds := ⟨differential.numerator.scale differential.scale, left.val, right.val⟩) //
    budget = ContactBudget.build first last target positive
      (bounds := ⟨differential.numerator.scale differential.scale, left.val, right.val⟩)}

/-- Compute the genuine polynomial ceilings and both original face/grid floors before any model or corner reading. -/
def preparePolynomial (ordinary : differential.denominatorPairs = 0)
    (target : Rational) (positive : 0 < target) :
    PolynomialPreparation first last differential target positive :=
  let left := PrimitiveOverlapBounds.build firstFace.clearance (differential.numerator.scale differential.scale)
  let right := PrimitiveOverlapBounds.build lastFace.clearance (differential.numerator.scale differential.scale)
  let budget := ContactBudget.build first last target positive
    (bounds := ⟨differential.numerator.scale differential.scale, left, right⟩)
  ⟨⟨(), ordinary⟩, ⟨left, rfl⟩, ⟨right, rfl⟩, ⟨budget, rfl⟩⟩

namespace PolynomialPreparation

variable {first last differential} {target : Rational} {positive : 0 < target}
    (retained : PolynomialPreparation first last differential target positive)

/-- Read the genuine polynomial overlap bounds constructed on the original first-face clearance. -/
@[expose] def leftBounds : PrimitiveOverlapBounds firstFace.clearance
    (differential.numerator.scale differential.scale) := retained.2.1.val

/-- Read the genuine polynomial overlap bounds constructed on the independent original second-face clearance. -/
@[expose] def rightBounds : PrimitiveOverlapBounds lastFace.clearance
    (differential.numerator.scale differential.scale) := retained.2.2.1.val

/-- The complete first bound cache is its original P-specific constructor on that SAME clearance. -/
theorem leftBounds_eq : retained.leftBounds = PrimitiveOverlapBounds.build firstFace.clearance
    (differential.numerator.scale differential.scale) := retained.2.1.property

/-- The complete second bound cache is its original P-specific constructor on that SAME clearance. -/
theorem rightBounds_eq : retained.rightBounds = PrimitiveOverlapBounds.build lastFace.clearance
    (differential.numerator.scale differential.scale) := retained.2.2.1.property

/-- Read the SAME original full-P contact budget on the two actual retained clearance owners. -/
@[expose] def budget : ContactBudget first last target
    (bounds := ⟨differential.numerator.scale differential.scale, retained.leftBounds, retained.rightBounds⟩) :=
  retained.2.2.2.val

/-- The whole supplied common budget is its sole original constructor on the two retained genuine P bounds. -/
theorem budget_eq : retained.budget = ContactBudget.build first last target positive
    (bounds := ⟨differential.numerator.scale differential.scale, retained.leftBounds, retained.rightBounds⟩) :=
  retained.2.2.2.property

include retained in
/-- The retained specification is genuinely ordinary, with the original polynomial numerator and scalar. -/
theorem ordinary : differential.denominatorPairs = 0 := retained.1.property

/-- The retained common source floor pays the actual first-face analytic floor. -/
theorem left_source_le : retained.budget.left.minimumIndex ≤ retained.budget.minimum :=
  (Data.Nat.Order.le_max_left _ _).trans_eq retained.budget.minimum_eq.symm

/-- The retained common source floor pays the actual second-face analytic floor. -/
theorem right_source_le : retained.budget.right.minimumIndex ≤ retained.budget.minimum :=
  (Data.Nat.Order.le_max_right _ _).trans_eq retained.budget.minimum_eq.symm

end PolynomialPreparation

variable {first last differential} {target : Rational} {positive : 0 < target}
    (retained : PolynomialPreparation first last differential target positive)
    {index : Nat}
    (leftData : DomainPrimitives first.domain basis index
      (numerator := differential.numerator.scale differential.scale))
    (rightData : DomainPrimitives last.domain basis index
      (numerator := differential.numerator.scale differential.scale))
    (later : retained.budget.index ≤ index)

/-- The original common P model bank and same-data entered-mesh reading caches, with complete factories. -/
@[expose] def PolynomialComparison : Type _ :=
  {_value : DomainPrimitives first.domain basis index
    (numerator := differential.numerator.scale differential.scale) // _value = leftData} ×
  {_value : DomainPrimitives last.domain basis index
    (numerator := differential.numerator.scale differential.scale) // _value = rightData} ×
  (work : {value : PolynomialWork first.cache.covered retained.budget.minimum differential //
    value = PolynomialWork.build first.cache.covered retained.budget.minimum differential}) ×
  (models : {value : work.val.Models 0 // value = work.val.models 0}) ×
  (_left : {value : SharedPrimitiveValues leftData.anchors leftData.offsets first.mesh.mesh.surface //
    value = SharedPrimitiveValues.build leftData.anchors leftData.offsets first.mesh.mesh.surface}) ×
  (_right : {value : SharedPrimitiveValues rightData.anchors rightData.offsets last.mesh.mesh.surface //
    value = SharedPrimitiveValues.build rightData.anchors rightData.offsets last.mesh.mesh.surface}) ×
  {common : Canonical // common =
    (PathModel.mk (PolynomialWork.Models.cells first.cache.covered work.val models.val)).integralSample}

/-- Build one actual ordinary-P common model bank and both entered-mesh scalar reading caches from the GIVEN primitives.

The whole supplied face primitive data are never rebuilt. The second face
uses the same common source models through joint original parent-list
transport in the accuracy theorem, independently of its covering cache.
-/
def comparePolynomial : PolynomialComparison retained leftData rightData :=
  let work := PolynomialWork.build first.cache.covered retained.budget.minimum differential
  let models := work.models 0
  let left := SharedPrimitiveValues.build leftData.anchors leftData.offsets first.mesh.mesh.surface
  let right := SharedPrimitiveValues.build rightData.anchors rightData.offsets last.mesh.mesh.surface
  let common := (PathModel.mk (PolynomialWork.Models.cells first.cache.covered work models)).integralSample
  ⟨⟨leftData, rfl⟩, ⟨rightData, rfl⟩, ⟨work, rfl⟩, ⟨models, rfl⟩,
    ⟨left, rfl⟩, ⟨right, rfl⟩, ⟨common, rfl⟩⟩

namespace PolynomialComparison

variable {retained leftData rightData} (compared : PolynomialComparison retained leftData rightData)

/-- Read the SAME whole supplied first-face P primitive cache, including its original anchors, offsets and corners. -/
@[expose] def leftInput : DomainPrimitives first.domain basis index
    (numerator := differential.numerator.scale differential.scale) := compared.1.val

/-- Read the SAME whole supplied second-face P primitive cache with its independent primitive constants. -/
@[expose] def rightInput : DomainPrimitives last.domain basis index
    (numerator := differential.numerator.scale differential.scale) := compared.2.1.val

/-- The retained first-face input is the whole GIVEN cache, rather than a reconstructed primitive bank. -/
theorem leftInput_eq : compared.leftInput = leftData := compared.1.property

/-- The retained second-face input is the whole GIVEN independent cache. -/
theorem rightInput_eq : compared.rightInput = rightData := compared.2.1.property

/-- Read the same original common work cache on the original first-face source cover. -/
@[expose] def work : PolynomialWork first.cache.covered retained.budget.minimum differential := compared.2.2.1.val

/-- Read the SAME original ordinary-P models selected after the common source floor, without another model call. -/
@[expose] def models : compared.work.Models 0 := compared.2.2.2.1.val

/-- Read the same actual first entered-mesh values of the supplied first-face primitive data. -/
@[expose] def left : SharedPrimitiveValues leftData.anchors leftData.offsets first.mesh.mesh.surface :=
  compared.2.2.2.2.1.val

/-- Read the same actual second entered-mesh values of the supplied second-face primitive data. -/
@[expose] def right : SharedPrimitiveValues rightData.anchors rightData.offsets last.mesh.mesh.surface :=
  compared.2.2.2.2.2.1.val

/-- Read the one cached scalar integral of that SAME complete original common P model bank. -/
@[expose] def common : Canonical := compared.2.2.2.2.2.2.val

/-- The retained common work is the original constructor on the SAME given covering cache and selected floor. -/
theorem work_eq : compared.work = PolynomialWork.build first.cache.covered retained.budget.minimum differential :=
  compared.2.2.1.property

/-- The whole common model bank is the sole original model construction after that common source floor. -/
theorem models_eq : compared.models = compared.work.models 0 := compared.2.2.2.1.property

/-- The actual left entered-mesh scalar readings consume the supplied first-face anchors and offsets exactly. -/
theorem left_eq : compared.left =
    SharedPrimitiveValues.build leftData.anchors leftData.offsets first.mesh.mesh.surface := compared.2.2.2.2.1.property

/-- The actual right entered-mesh scalar readings consume the supplied second-face data exactly. -/
theorem right_eq : compared.right =
    SharedPrimitiveValues.build rightData.anchors rightData.offsets last.mesh.mesh.surface :=
  compared.2.2.2.2.2.1.property

/-- The common scalar is the exact integral of those actual original cells and primitive constants. -/
theorem common_eq : compared.common =
    (PathModel.mk (PolynomialWork.Models.cells first.cache.covered compared.work compared.models)).integralSample :=
  compared.2.2.2.2.2.2.property

include compared later in
/-- Two actual point-reading caches at the partial path endpoints obey the retained genuine-P contact request.

Both increments compare to the SAME retained common work and model bank.
The original joint parent-list transport is used on the second face, and
all actual primitive constants, owners, endpoint slots and stages remain
independent. No corner or whole-edge replacement is required.
-/
theorem points_accurate {leftCount rightCount : Nat}
    {leftPoint : Fin leftCount → Canonical} {rightPoint : Fin rightCount → Canonical}
    (leftPoints : PointReadings leftData.anchors leftData.offsets leftPoint)
    (rightPoints : PointReadings rightData.anchors rightData.offsets rightPoint)
    (leftStart leftFinish : Fin leftCount) (rightStart rightFinish : Fin rightCount)
    (leftStartEq : leftPoint leftStart = start) (leftFinishEq : leftPoint leftFinish = finish)
    (rightStartEq : rightPoint rightStart = start) (rightFinishEq : rightPoint rightFinish = finish) :
    normSq ((leftPoints.values leftFinish - leftPoints.values leftStart) -
      (rightPoints.values rightFinish - rightPoints.values rightStart)) < target := by
  let leftBudget := retained.budget.left.atGridIndex index (retained.budget.left_later
    (bounds := ⟨differential.numerator.scale differential.scale, retained.leftBounds, retained.rightBounds⟩) later)
  let rightBudget := retained.budget.right.atGridIndex index (retained.budget.right_later
    (bounds := ⟨differential.numerator.scale differential.scale, retained.leftBounds, retained.rightBounds⟩) later)
  have leftRaw := first.polynomial_points_lt leftBudget first.cache.covered compared.work compared.models
    retained.left_source_le compared.left leftPoints leftStart leftFinish leftStartEq leftFinishEq
    retained.budget.tolerance rfl
  have left : normSq ((leftPoints.values leftFinish - leftPoints.values leftStart) - compared.common) <
      retained.budget.tolerance := Eq.mpr (congrArg (fun common : Canonical =>
    normSq ((leftPoints.values leftFinish - leftPoints.values leftStart) - common) <
      retained.budget.tolerance) compared.common_eq) leftRaw
  have same : first.cache.parents = last.cache.parents := first.cache.parents_eq.trans last.cache.parents_eq.symm
  have rightRaw : normSq ((rightPoints.values rightFinish - rightPoints.values rightStart) -
      (PathModel.mk (PolynomialWork.Models.cells first.cache.covered compared.work compared.models)).integralSample) <
      retained.budget.tolerance :=
    PolynomialWork.Models.withParents same first.cache.covered compared.work compared.models
      (fun covered _ _ work _ models _ sampleEq => by
        have actual := last.polynomial_points_lt rightBudget covered work models
          retained.right_source_le compared.right rightPoints rightStart rightFinish rightStartEq rightFinishEq
          retained.budget.tolerance rfl
        exact Eq.mp (congrArg (fun common : Canonical => normSq
          ((rightPoints.values rightFinish - rightPoints.values rightStart) - common) <
            retained.budget.tolerance) sampleEq) actual)
  have right : normSq ((rightPoints.values rightFinish - rightPoints.values rightStart) - compared.common) <
      retained.budget.tolerance := Eq.mpr (congrArg (fun common : Canonical =>
    normSq ((rightPoints.values rightFinish - rightPoints.values rightStart) - common) <
      retained.budget.tolerance) compared.common_eq) rightRaw
  let common := compared.common
  have identity : (leftPoints.values leftFinish - leftPoints.values leftStart) -
      (rightPoints.values rightFinish - rightPoints.values rightStart) =
      ((leftPoints.values leftFinish - leftPoints.values leftStart) - common) -
        ((rightPoints.values rightFinish - rightPoints.values rightStart) - common) := by ring1
  rewrite [identity]
  have original := Norm.Bounds.normSq_sub_le_two
    ((leftPoints.values leftFinish - leftPoints.values leftStart) - common)
    ((rightPoints.values rightFinish - rightPoints.values rightStart) - common)
  have paid := original.trans_lt (Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide +kernel)
    (Order.Arithmetic.add_lt_add_direct left right))
  exact paid.trans_eq (by
    rewrite [retained.budget.tolerance_eq]
    change 2 * (target / 4 + target / 4) = target
    rewrite [show 2 * (target / 4 + target / 4) = (target / 4) * 4 by ring1]
    exact Field.div_mul_cancel_of_ne _ _ (by decide +kernel))

include compared later in
/-- The actual P face corners at the given later shared stage differ by less than the original contact request.

Both faces compare internally to the SAME genuine P model bank. The
original parent-list identities transport that whole common source, and
finite squared-norm bounds cancel only its identical scalar reading.
No holomorphic differential programme or wanted P discrepancy is assumed.
-/
theorem accurate (leftStart leftFinish rightStart rightFinish : Fin 4)
    (leftStartEq : FaceCorners.point firstFace.cell.box leftStart = start)
    (leftFinishEq : FaceCorners.point firstFace.cell.box leftFinish = finish)
    (rightStartEq : FaceCorners.point lastFace.cell.box rightStart = start)
    (rightFinishEq : FaceCorners.point lastFace.cell.box rightFinish = finish) :
    normSq ((leftData.corners.values leftFinish - leftData.corners.values leftStart) -
      (rightData.corners.values rightFinish - rightData.corners.values rightStart)) < target :=
  PolynomialComparison.points_accurate (retained := retained) (leftData := leftData)
    (rightData := rightData) (later := later) compared leftData.corners rightData.corners
    leftStart leftFinish rightStart rightFinish leftStartEq leftFinishEq rightStartEq rightFinishEq

end PolynomialComparison

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests.ContactBudget
