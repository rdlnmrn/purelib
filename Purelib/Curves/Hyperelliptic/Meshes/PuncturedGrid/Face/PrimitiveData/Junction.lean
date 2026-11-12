module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContinuedComparison.Junction
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Comparison.RectangularSharedPrimitiveComparison
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularPrimitiveOverlap
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring
import Purelib.Approximation.Rational.Geometric.Basic

/-! # Actual cross-domain primitive anchor drift at a signed junction

The two old primitive/PointReading/Point/Entry caches remain distinct.
A finite coverage check either prepares the original signed transition
and anchor or retains the exact selected-cell subdivision request. The
computed primitive gap includes both old offsets and is never set to zero.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives

open Purelib
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Riemann.Integration
open Purelib.Riemann.Normalization
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.TransportedFaceInverseModels (TransportedCell)
open Purelib.Riemann.Normalization.InverseModelEdgeTransition (EdgeTransition)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Paths.OwnerTraceReadings (OwnerJoin)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds PrimitiveEdgeAnchor)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {frames : RootFrames bank.grid}

variable {numerator : CoefficientPolynomial}

section OneDomain

variable {face : RegularFace bank} {models : FaceModels frames face} {sheet : Fin 2}
variable {domain : PeriodDomain models sheet} {differential : Differential genus} {index size : Nat}
variable {points : Fin size → Canonical}
variable (data : DomainPrimitives domain differential index (numerator := numerator))
variable (readings : PointReadings data.anchors data.offsets points) (position : Fin size)

/-- Read the original transported model cell selected by one actual retained numerical point owner. -/
def readingCell : TransportedCell models.bounds (models.frame.owners sheet)
    (domain.geometry.box (readings.owners position).column (readings.owners position).row) :=
  domain.patch.transported.cell (readings.owners position).column (readings.owners position).row

/-- The retained original point owner supplies its actual selected cell containment. -/
theorem readingCell_inside {point : Canonical} (same : points position = point) :
    (domain.geometry.box (readings.owners position).column (readings.owners position).row).Contains point :=
  Eq.mp (congrArg (domain.geometry.box (readings.owners position).column (readings.owners position).row).Contains
    ((readings.point_eq position).trans same)) (readings.owners position).contains

/-- Read the cached scalar at its actual selected old primitive cell, preserving the original offset. -/
theorem readingCell_value {point : Canonical} (same : points position = point) : readings.values position =
    data.anchors.alignedValue data.offsets (readings.owners position).column (readings.owners position).row point :=
  (readings.value_eq position).trans
    (congrArg (data.anchors.alignedValue data.offsets (readings.owners position).column
      (readings.owners position).row) ((readings.point_eq position).trans same))

end OneDomain

namespace Junction

variable {leftFace rightFace : RegularFace bank}
variable {leftModels : FaceModels frames leftFace} {rightModels : FaceModels frames rightFace}
variable {start finish : Canonical} {leftCount rightCount : Nat}
variable {leftPatch : ContinuedNeighborhood curve.polynomial leftCount}
variable {rightPatch : ContinuedNeighborhood curve.polynomial rightCount}
variable (leftPoint : ContinuedNeighborhood.Point leftPatch start)
variable (rightPoint : ContinuedNeighborhood.Point rightPatch start)
variable (leftPointInside : leftPatch.box.Contains start)
variable (leftEntry : Entry leftModels start leftPoint.owner) (rightEntry : Entry rightModels start rightPoint.owner)
variable (joined : OwnerJoin leftPoint.owner rightPoint.owner)
variable {leftDomain : PeriodDomain leftModels leftEntry.sheet}
variable {rightDomain : PeriodDomain rightModels rightEntry.sheet} {differential : Differential genus}
variable {leftIndex rightIndex leftSize rightSize : Nat}
variable (leftData : DomainPrimitives leftDomain differential leftIndex (numerator := numerator))
variable (rightData : DomainPrimitives rightDomain differential rightIndex (numerator := numerator))
variable {leftPoints : Fin leftSize → Canonical} {rightPoints : Fin rightSize → Canonical}
variable (leftReadings : PointReadings leftData.anchors leftData.offsets leftPoints)
variable (rightReadings : PointReadings rightData.anchors rightData.offsets rightPoints)
variable (leftFirst : Fin leftSize) (rightFirst : Fin rightSize)
variable (leftStart : leftPoints leftFirst = start) (rightStart : rightPoints rightFirst = start)

/-- Both selected old cells contain the requested whole comparison endpoint.

The start incidences come from the retained PointReading owners. Failure
requests a common subdivision of these actual two old cells, rather than
claiming that the old face, path, Point or primitive bank is invalid.
-/
abbrev EndInside {leftSheet rightSheet : Fin 2}
    {leftDomain : PeriodDomain leftModels leftSheet} {rightDomain : PeriodDomain rightModels rightSheet}
    {differential : Differential genus} {leftIndex rightIndex leftSize rightSize : Nat}
    (leftData : DomainPrimitives leftDomain differential leftIndex (numerator := numerator))
    (rightData : DomainPrimitives rightDomain differential rightIndex (numerator := numerator))
    {leftPoints : Fin leftSize → Canonical} {rightPoints : Fin rightSize → Canonical}
    (leftReadings : PointReadings leftData.anchors leftData.offsets leftPoints)
    (rightReadings : PointReadings rightData.anchors rightData.offsets rightPoints)
    (leftFirst : Fin leftSize) (rightFirst : Fin rightSize) {finish : Canonical} : Prop :=
  (leftDomain.geometry.box (leftReadings.owners leftFirst).column
    (leftReadings.owners leftFirst).row).Contains finish ∧
  (rightDomain.geometry.box (rightReadings.owners rightFirst).column
    (rightReadings.owners rightFirst).row).Contains finish

/-- Exact original transition, overlap-bound and primitive-anchor caches on these two actual selected cells. -/
abbrev Preparation (covered : EndInside leftData rightData leftReadings rightReadings leftFirst rightFirst
    (finish := finish)) :=
  Σ _bounds : {value : PrimitiveOverlapBounds
      (leftFace.clearance.restrict
        (leftDomain.patch.cell_refines (leftReadings.owners leftFirst).column (leftReadings.owners leftFirst).row))
      numerator //
    value = PrimitiveOverlapBounds.build
      (leftFace.clearance.restrict
        (leftDomain.patch.cell_refines (leftReadings.owners leftFirst).column (leftReadings.owners leftFirst).row))
      numerator},
  Σ edge : {value : EdgeTransition ((leftData.readingCell leftReadings leftFirst).model.refine (leftIndex + 2))
      ((rightData.readingCell rightReadings rightFirst).model.refine (rightIndex + 2)) start finish //
    value = ContinuedComparison.junctionTransition leftPoint rightPoint leftPointInside leftEntry rightEntry joined
      differential (leftData.readingCell leftReadings leftFirst) (rightData.readingCell rightReadings rightFirst)
      (leftData.readingCell_inside leftReadings leftFirst leftStart)
      (rightData.readingCell_inside rightReadings rightFirst rightStart) leftIndex rightIndex covered.1 covered.2},
  {value : PrimitiveEdgeAnchor edge.val
      (leftData.primitives.dense (leftReadings.owners leftFirst).column
        (leftReadings.owners leftFirst).row).value
      (rightData.primitives.dense (rightReadings.owners rightFirst).column
        (rightReadings.owners rightFirst).row).value //
    value = PrimitiveEdgeAnchor.build edge.val
      (leftData.primitives.dense (leftReadings.owners leftFirst).column (leftReadings.owners leftFirst).row).value
      (rightData.primitives.dense (rightReadings.owners rightFirst).column (rightReadings.owners rightFirst).row).value}

/-- Prepare actual cell comparisons and the real start offset once, using the existing signed junction. -/
def prepare (covered : EndInside leftData rightData leftReadings rightReadings leftFirst rightFirst
    (finish := finish)) : Preparation leftPoint rightPoint leftPointInside leftEntry rightEntry joined
      leftData rightData leftReadings rightReadings leftFirst rightFirst leftStart rightStart covered :=
  let bounds := PrimitiveOverlapBounds.build
    (leftFace.clearance.restrict
      (leftDomain.patch.cell_refines (leftReadings.owners leftFirst).column (leftReadings.owners leftFirst).row))
    numerator
  let edge := ContinuedComparison.junctionTransition leftPoint rightPoint leftPointInside leftEntry rightEntry joined
    differential (leftData.readingCell leftReadings leftFirst) (rightData.readingCell rightReadings rightFirst)
    (leftData.readingCell_inside leftReadings leftFirst leftStart)
    (rightData.readingCell_inside rightReadings rightFirst rightStart) leftIndex rightIndex covered.1 covered.2
  let anchor := PrimitiveEdgeAnchor.build edge
    (leftData.primitives.dense (leftReadings.owners leftFirst).column (leftReadings.owners leftFirst).row).value
    (rightData.primitives.dense (rightReadings.owners rightFirst).column (rightReadings.owners rightFirst).row).value
  ⟨⟨bounds, rfl⟩, ⟨edge, rfl⟩, ⟨anchor, rfl⟩⟩

/-- The finite preparation outcome retains both complete old domains, observations and literal junction inputs.

Success keeps the actual transition/anchor caches. Inconclusivity retains
the exact attempted endpoints and failure of coverage in the two selected
old cells. Neither branch upgrades any old observation stage.
-/
abbrev Attempt :=
  {value : DomainPrimitives leftDomain differential leftIndex (numerator := numerator) ×
      DomainPrimitives rightDomain differential rightIndex
        (numerator := numerator) ×
      PointReadings leftData.anchors leftData.offsets leftPoints ×
      PointReadings rightData.anchors rightData.offsets rightPoints ×
      ContinuedNeighborhood.Point leftPatch start × ContinuedNeighborhood.Point rightPatch start ×
      Entry leftModels start leftPoint.owner × Entry rightModels start rightPoint.owner ×
      OwnerJoin leftPoint.owner rightPoint.owner × (Fin leftSize × Fin rightSize) ×
      (Canonical × Canonical) × (Nat × Nat) //
    value = (leftData, rightData, leftReadings, rightReadings, leftPoint, rightPoint, leftEntry, rightEntry, joined,
      (leftFirst, rightFirst), (start, finish), (leftIndex, rightIndex))} ×
  ((Σ covered : {_value : Unit // EndInside leftData rightData leftReadings rightReadings leftFirst rightFirst
      (finish := finish)},
    {value : Preparation leftPoint rightPoint leftPointInside leftEntry rightEntry joined leftData rightData
        leftReadings rightReadings leftFirst rightFirst leftStart rightStart covered.property //
      value = prepare leftPoint rightPoint leftPointInside leftEntry rightEntry joined leftData rightData
        leftReadings rightReadings leftFirst rightFirst leftStart rightStart covered.property}) ⊕
    {_value : Unit //
      ¬EndInside leftData rightData leftReadings rightReadings leftFirst rightFirst (finish := finish)})

/-- Check the actual selected-cell endpoint incidence and prepare only a fully supported comparison.

All retained caches survive either outcome. This is a finite geometric
check, not a query/Point/Entry execution or final comparison premise.
-/
def attempt : Attempt leftPoint rightPoint leftPointInside leftEntry rightEntry joined leftData rightData
    leftReadings rightReadings leftFirst rightFirst leftStart rightStart (finish := finish) :=
  let originals := (leftData, rightData, leftReadings, rightReadings, leftPoint, rightPoint,
    leftEntry, rightEntry, joined,
    (leftFirst, rightFirst), (start, finish), (leftIndex, rightIndex))
  letI : Decidable (EndInside leftData rightData leftReadings rightReadings leftFirst rightFirst
      (finish := finish)) := by
    unfold EndInside Geometry.Rational.Box.Contains
    infer_instance
  if covered : EndInside leftData rightData leftReadings rightReadings leftFirst rightFirst (finish := finish) then
    let prepared := prepare leftPoint rightPoint leftPointInside leftEntry rightEntry joined leftData rightData
      leftReadings rightReadings leftFirst rightFirst leftStart rightStart covered
    (⟨originals, rfl⟩, Sum.inl ⟨⟨(), covered⟩, ⟨prepared, rfl⟩⟩)
  else (⟨originals, rfl⟩, Sum.inr ⟨(), covered⟩)

namespace Preparation

variable {leftPoint rightPoint leftPointInside leftEntry rightEntry joined leftData rightData}
variable {leftReadings rightReadings leftFirst rightFirst leftStart rightStart}
variable {covered : EndInside leftData rightData leftReadings rightReadings leftFirst rightFirst (finish := finish)}
variable (prepared : Preparation leftPoint rightPoint leftPointInside leftEntry rightEntry joined leftData rightData
  leftReadings rightReadings leftFirst rightFirst leftStart rightStart covered)

/-- Read the whole original overlap-bound factory on the selected left cell and same differential. -/
def bounds : PrimitiveOverlapBounds
    (leftFace.clearance.restrict
      (leftDomain.patch.cell_refines (leftReadings.owners leftFirst).column (leftReadings.owners leftFirst).row))
    numerator := prepared.1.val

/-- Read the original unflipped transition built from the literal cached junction. -/
def edge : EdgeTransition ((leftData.readingCell leftReadings leftFirst).model.refine (leftIndex + 2))
    ((rightData.readingCell rightReadings rightFirst).model.refine (rightIndex + 2)) start finish := prepared.2.1.val

/-- Read the whole original primitive-anchor cache, retaining its actual nonzero offset. -/
def anchor : PrimitiveEdgeAnchor prepared.edge
    (leftData.primitives.dense (leftReadings.owners leftFirst).column (leftReadings.owners leftFirst).row).value
    (rightData.primitives.dense (rightReadings.owners rightFirst).column (rightReadings.owners rightFirst).row).value :=
  prepared.2.2.val

/-- The computed endpoint gap retains BOTH old global primitive offsets and the actual raw primitive anchor. -/
def gap : Canonical :=
  leftData.offsets.values (leftReadings.owners leftFirst).column (leftReadings.owners leftFirst).row -
    rightData.offsets.values (rightReadings.owners rightFirst).column (rightReadings.owners rightFirst).row +
      prepared.anchor.offset

/-- The cached original two-model residual formula is an explicit finite increment allowance. -/
def charge : Rational :=
  12 * (Geometric.Basic.quarterRadius
      (leftData.readingCell leftReadings leftFirst).model.bound (leftIndex + 2) +
    Geometric.Basic.quarterRadius
      (rightData.readingCell rightReadings rightFirst).model.bound (rightIndex + 2)) *
      (prepared.bounds.numeratorUpper * prepared.bounds.inverseUpper) * Norm.Basic.normSq (finish - start)

/-- The actual derived transition retains the unflipped old-sheet sign. -/
theorem sign_eq : prepared.edge.sign = 1 :=
  (congrArg (fun value => value.sign) prepared.2.1.property).trans
    (ContinuedComparison.junctionTransition_sign leftPoint rightPoint leftPointInside leftEntry rightEntry joined
      differential (leftData.readingCell leftReadings leftFirst) (rightData.readingCell rightReadings rightFirst)
      (leftData.readingCell_inside leftReadings leftFirst leftStart)
      (rightData.readingCell_inside rightReadings rightFirst rightStart) leftIndex rightIndex covered.1 covered.2)

/-- The computed gap is the actual old reading difference at the retained start, not zero normalization. -/
theorem gap_eq : prepared.gap = leftReadings.values leftFirst - rightReadings.values rightFirst := by
  rw [leftData.readingCell_value leftReadings leftFirst leftStart,
    rightData.readingCell_value rightReadings rightFirst rightStart]
  unfold gap
  rw [prepared.anchor.offset_eq, prepared.sign_eq]
  unfold RectangularPrimitiveGluing.PrimitiveAnchors.alignedValue
    RectangularPrimitiveModels.Primitives.dense
    RectangularPrimitiveModels.Primitives.value
  simp only [Data.Gaussian.Basic.one_mul]
  ring1

/-- The original anchor comparison pays the change of the computed inter-domain gap along the actual common edge. -/
theorem gap_drift_le :
    Norm.Basic.normSq ((leftData.anchors.alignedValue leftData.offsets (leftReadings.owners leftFirst).column
        (leftReadings.owners leftFirst).row finish -
      rightData.anchors.alignedValue rightData.offsets (rightReadings.owners rightFirst).column
        (rightReadings.owners rightFirst).row finish) - prepared.gap) ≤ prepared.charge := by
  have bound := PrimitiveEdgeAnchor.drift_le (pairs := 0) prepared.bounds
    (leftData.primitives.dense (leftReadings.owners leftFirst).column (leftReadings.owners leftFirst).row)
    (rightData.primitives.dense (rightReadings.owners rightFirst).column (rightReadings.owners rightFirst).row)
    prepared.anchor
    (leftDomain.patch.primitive_coefficient_eq (pairs := 0)
      (entered := TracedPath.build
        (ClearPath.nil (polynomial := curve.polynomial) (ambient := leftFace.cell.box) leftFace.cell.box.anchor)
        (.nil leftFace.cell.box.anchor) _)
      leftFace.cell.box.contains_anchor differential (BranchIsolation.degreePositive curve)
      (LoopMonodromy.BranchCellBank.referenceAt bank _ (leftFace.cell.anchor_mem leftFace.member)).toLoop
      leftData.primitives
      (leftReadings.owners leftFirst).column (leftReadings.owners leftFirst).row)
    (rightDomain.patch.primitive_coefficient_eq (pairs := 0)
      (entered := TracedPath.build
        (ClearPath.nil (polynomial := curve.polynomial) (ambient := rightFace.cell.box) rightFace.cell.box.anchor)
        (.nil rightFace.cell.box.anchor) _)
      rightFace.cell.box.contains_anchor differential (BranchIsolation.degreePositive curve)
      (LoopMonodromy.BranchCellBank.referenceAt bank _ (rightFace.cell.anchor_mem rightFace.member)).toLoop
      rightData.primitives
      (rightReadings.owners rightFirst).column (rightReadings.owners rightFirst).row)
    (parameter := 1) (⟨of_decide_eq_true rfl, Basic.le_refl 1⟩ : (0 : Rational) ≤ 1 ∧ (1 : Rational) ≤ 1)
  rewrite [PrimitiveOverlapBounds.weight_zero] at bound
  simp only [InverseModelEdgeTransition.line_one, PrimitiveEdgeAnchor.alignedValue,
    prepared.sign_eq, Data.Gaussian.Basic.one_mul] at bound
  unfold charge gap
  rw [InverseRootPolynomial.Model.refine_bound, InverseRootPolynomial.Model.refine_bound] at bound
  unfold RectangularPrimitiveGluing.PrimitiveAnchors.alignedValue
  unfold RectangularPrimitiveModels.Primitives.dense at bound
  unfold RectangularPrimitiveModels.Primitives.value
  have scalar :
      (leftData.offsets.values (leftReadings.owners leftFirst).column (leftReadings.owners leftFirst).row +
          (leftData.primitives.cells (leftReadings.owners leftFirst).column
            (leftReadings.owners leftFirst).row).value.eval finish -
        (rightData.offsets.values (rightReadings.owners rightFirst).column (rightReadings.owners rightFirst).row +
          (rightData.primitives.cells (rightReadings.owners rightFirst).column
            (rightReadings.owners rightFirst).row).value.eval finish)) -
        (leftData.offsets.values (leftReadings.owners leftFirst).column (leftReadings.owners leftFirst).row -
          rightData.offsets.values (rightReadings.owners rightFirst).column (rightReadings.owners rightFirst).row +
            prepared.anchor.offset) =
      (leftData.primitives.cells (leftReadings.owners leftFirst).column
        (leftReadings.owners leftFirst).row).value.eval finish -
        (prepared.anchor.offset + (rightData.primitives.cells (rightReadings.owners rightFirst).column
          (rightReadings.owners rightFirst).row).value.eval finish) := by ring1
  rw [scalar]
  simpa only [Norm.Basic.normSq_eq_canonical] using bound

section EndpointReadings

variable (leftLast : Fin leftSize) (rightLast : Fin rightSize)
variable (leftFinish : leftPoints leftLast = finish) (rightFinish : rightPoints rightLast = finish)

/-- Retain actual endpoint occurrences and their two computed ownership errors with the full finite comparison bound.

The source reading values, selected-cell aligned endpoints and original
model charge remain distinct. Endpoint errors are computed, never set to
zero or identified with root-expression observation errors.
-/
abbrev EndpointErrors :=
  {value : Fin leftSize × Fin rightSize // value = (leftLast, rightLast)} ×
  {_value : Unit // leftPoints leftLast = finish ∧ rightPoints rightLast = finish} ×
  {value : Canonical × Canonical // value =
    (leftData.anchors.alignedValue leftData.offsets (leftReadings.owners leftFirst).column
      (leftReadings.owners leftFirst).row finish,
    rightData.anchors.alignedValue rightData.offsets (rightReadings.owners rightFirst).column
      (rightReadings.owners rightFirst).row finish)} ×
  (Σ errors : {value : Canonical × Canonical // value =
      (leftReadings.values leftLast -
        leftData.anchors.alignedValue leftData.offsets (leftReadings.owners leftFirst).column
          (leftReadings.owners leftFirst).row finish,
      rightReadings.values rightLast -
        rightData.anchors.alignedValue rightData.offsets (rightReadings.owners rightFirst).column
          (rightReadings.owners rightFirst).row finish)},
  {value : Rational // value = 4 * Norm.Basic.normSq errors.val.1 + 4 * prepared.charge +
    2 * Norm.Basic.normSq errors.val.2})

/-- Evaluate the two aligned endpoints once and compute the original readings' actual finite error allowance. -/
def endpointErrors : prepared.EndpointErrors leftLast rightLast :=
  let first := leftData.anchors.alignedValue leftData.offsets (leftReadings.owners leftFirst).column
    (leftReadings.owners leftFirst).row finish
  let last := rightData.anchors.alignedValue rightData.offsets (rightReadings.owners rightFirst).column
    (rightReadings.owners rightFirst).row finish
  let leftError := leftReadings.values leftLast - first
  let rightError := rightReadings.values rightLast - last
  let bound := 4 * Norm.Basic.normSq leftError + 4 * prepared.charge + 2 * Norm.Basic.normSq rightError
  (⟨(leftLast, rightLast), rfl⟩, ⟨(), leftFinish, rightFinish⟩,
    ⟨(first, last), rfl⟩, ⟨⟨(leftError, rightError), rfl⟩, ⟨bound, rfl⟩⟩)

namespace EndpointErrors

variable {prepared leftLast rightLast} (errors : prepared.EndpointErrors leftLast rightLast)

/-- Read both actual computed endpoint-owner discrepancies without evaluating primitives again. -/
def values : Canonical × Canonical := errors.2.2.2.1.val

/-- Read the original finite allowance computed from those SAME discrepancies and the model comparison charge. -/
def bound : Rational := errors.2.2.2.2.val

/-- The retained ownership errors are their complete original scalar factory. -/
theorem values_eq : errors.values =
    (leftReadings.values leftLast -
      leftData.anchors.alignedValue leftData.offsets (leftReadings.owners leftFirst).column
        (leftReadings.owners leftFirst).row finish,
    rightReadings.values rightLast -
      rightData.anchors.alignedValue rightData.offsets (rightReadings.owners rightFirst).column
        (rightReadings.owners rightFirst).row finish) := errors.2.2.2.1.property

/-- The allowance retains the actual two endpoint errors and the derived original model charge. -/
theorem bound_eq : errors.bound =
    4 * Norm.Basic.normSq errors.values.1 + 4 * prepared.charge + 2 * Norm.Basic.normSq errors.values.2 :=
  errors.2.2.2.2.property

/-- The original two retained reading increments differ by at most the computed finite allowance.

This pays the actual computed endpoint ownership changes and the genuine
cross-domain primitive drift. It assumes neither absolute normalization
nor closeness of the original two numerical readings.
-/
theorem increment_le : Norm.Basic.normSq ((leftReadings.values leftLast - leftReadings.values leftFirst) -
    (rightReadings.values rightLast - rightReadings.values rightFirst)) ≤ errors.bound := by
  let middle :=
    (leftData.anchors.alignedValue leftData.offsets (leftReadings.owners leftFirst).column
      (leftReadings.owners leftFirst).row finish -
      rightData.anchors.alignedValue rightData.offsets (rightReadings.owners rightFirst).column
        (rightReadings.owners rightFirst).row finish) - prepared.gap
  have model : Norm.Basic.normSq middle ≤ prepared.charge := prepared.gap_drift_le
  have identity : (leftReadings.values leftLast - leftReadings.values leftFirst) -
      (rightReadings.values rightLast - rightReadings.values rightFirst) =
      (errors.values.1 + middle) - errors.values.2 := by
    rw [errors.values_eq]
    dsimp only [middle]
    rw [prepared.gap_eq]
    ring1
  rw [identity]
  have inner := Norm.Bounds.normSq_add_le_two errors.values.1 middle
  have innerBound := inner.trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct (Basic.le_refl _) model)
      (of_decide_eq_true rfl : (0 : Rational) ≤ 2))
  have outer := Norm.Bounds.normSq_sub_le_two (errors.values.1 + middle) errors.values.2
  have total := outer.trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct innerBound (Basic.le_refl _))
      (of_decide_eq_true rfl : (0 : Rational) ≤ 2))
  exact total.trans_eq (by rw [errors.bound_eq]; ring1)

/-- Opposite signed boundary occurrences use the SAME endpoint caches and finite comparison allowance.

The right boundary increment is reversed algebraically. No path, root,
reading or endpoint owner is reversed or acquired by this operation.
-/
theorem opposite_increment_le :
    Norm.Basic.normSq ((leftReadings.values leftLast - leftReadings.values leftFirst) +
      (rightReadings.values rightFirst - rightReadings.values rightLast)) ≤ errors.bound := by
  have scalar : (leftReadings.values leftLast - leftReadings.values leftFirst) +
      (rightReadings.values rightFirst - rightReadings.values rightLast) =
      (leftReadings.values leftLast - leftReadings.values leftFirst) -
        (rightReadings.values rightLast - rightReadings.values rightFirst) := by ring1
  rw [scalar]
  exact errors.increment_le

/-- Retain the same finite error cache and target with either its actual successful payment or exact unpaid bound. -/
abbrev Payment (target : Rational) :=
  {value : prepared.EndpointErrors leftLast rightLast × Rational // value = (errors, target)} ×
  ({_value : Unit // errors.bound < target} ⊕ {_value : Unit // ¬errors.bound < target})

/-- Check the computed allowance on these unchanged old observation stages, without upgrading or rebuilding them. -/
def pay (target : Rational) : errors.Payment target :=
  if paid : errors.bound < target then (⟨(errors, target), rfl⟩, Sum.inl ⟨(), paid⟩)
  else (⟨(errors, target), rfl⟩, Sum.inr ⟨(), paid⟩)

/-- An actual sufficient scalar payment proves the original increment comparison at its retained target. -/
theorem paid {target : Rational} (paid : errors.bound < target) :
    Norm.Basic.normSq ((leftReadings.values leftLast - leftReadings.values leftFirst) -
      (rightReadings.values rightLast - rightReadings.values rightFirst)) < target :=
  errors.increment_le.trans_lt paid

end EndpointErrors

end EndpointReadings

end Preparation

namespace Attempt

variable {leftPoint rightPoint leftPointInside leftEntry rightEntry joined leftData rightData}
variable {leftReadings rightReadings leftFirst rightFirst leftStart rightStart}
variable (attempted : Attempt leftPoint rightPoint leftPointInside leftEntry rightEntry joined leftData rightData
  leftReadings rightReadings leftFirst rightFirst leftStart rightStart (finish := finish))

/-- A computed gap on the same successful preparation, or no scalar for its unresolved coverage request.

The success cache retains the original Preparation.gap and its exact
old-reading difference. Both old offsets and the raw primitive anchor
remain unchanged; the complete failure stays in the supplied Attempt.
-/
@[expose] def GapReading :=
  match attempted.2 with
  | Sum.inl ready =>
      {value : Canonical // value = ready.2.val.gap ∧
        value = leftReadings.values leftFirst - rightReadings.values rightFirst}
  | Sum.inr _ => Unit

/-- Compute the original preparation gap once, retaining its actual old-reading law without another attempt. -/
def readGap : GapReading attempted := by
  unfold GapReading
  cases attempted.2 with
  | inl ready =>
      let gap := ready.2.val.gap
      exact ⟨gap, rfl, ready.2.val.gap_eq⟩
  | inr _ => exact ()

/-- A displayed scalar equals the same successful preparation's original gap, excluding an uncovered outcome. -/
@[expose] def PreparedGap (value : Canonical) : Prop :=
  match attempted.2 with
  | Sum.inl ready => value = ready.2.val.gap
  | Sum.inr _ => False

/-- A successful gap from the actual supplied outcome and its two unchanged old reading occurrences.

Success identifies the scalar with that outcome's original Preparation.gap.
An uncovered outcome has no such scalar. No primitive constant is
normalized and no numerical closeness is part of this certificate.
-/
@[expose] def Gap :=
  {value : Canonical // value = leftReadings.values leftFirst - rightReadings.values rightFirst ∧
    PreparedGap attempted value}

/-- Extract the already cached gap when the same selected old cells cover the attempted endpoint.

The actual outcome and its given GapReading are consumed together.
The uncovered branch contradicts only its exact EndInside failure.
No attempt, preparation, anchor, primitive evaluation or reading is run.
-/
def gapOfCovered (reading : GapReading attempted)
    (covered : EndInside leftData rightData leftReadings rightReadings leftFirst rightFirst (finish := finish)) :
    Gap attempted := by
  unfold Gap PreparedGap
  refine Sum.casesOn
    (motive := fun outcome =>
      GapReading (attempted.1, outcome) →
      {value : Canonical // value = leftReadings.values leftFirst - rightReadings.values rightFirst ∧
        match outcome with
        | Sum.inl ready => value = ready.2.val.gap
        | Sum.inr _ => False})
    attempted.2 ?_ ?_ reading
  · intro ready reading
    unfold GapReading at reading
    exact ⟨reading.val, reading.property.2, reading.property.1⟩
  · intro uncovered _reading
    exact False.elim (uncovered.property covered)

end Attempt

end Junction

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives

end
