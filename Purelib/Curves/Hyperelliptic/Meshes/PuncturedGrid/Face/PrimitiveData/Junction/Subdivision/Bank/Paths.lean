module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.Junction.Subdivision.Bank
public import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Algebra.FiniteSum.Rational.Squares
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.NatCast
import Purelib.Tactic.Ring

/-! # Ordered common-domain readings along the original clear path

Every original segment retains its whole actual common-child bank. Adjacent
segments share the SAME old reading indices, including repeated or
stationary occurrences. The finite consumer sums their actual signed
discrepancies and charges, retaining every original unpaid child request.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives.Junction.Subdivision

namespace Bank

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Paths.OwnerTraceReadings (OwnerJoin)
open Purelib.Algebra.FiniteSum.Rational.Squares (coordinateSum)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {frames : RootFrames bank.grid} {leftFace rightFace : RegularFace bank}
variable {leftModels : FaceModels frames leftFace} {rightModels : FaceModels frames rightFace}
variable {leftSheet rightSheet : Fin 2}
variable {leftDomain : PeriodDomain leftModels leftSheet} {rightDomain : PeriodDomain rightModels rightSheet}
variable {differential : Differential genus} {leftStage rightStage : Nat}
variable {leftData : DomainPrimitives leftDomain differential leftStage}
variable {rightData : DomainPrimitives rightDomain differential rightStage}
variable {leftSize rightSize : Nat} {leftPoints : Fin leftSize → Canonical} {rightPoints : Fin rightSize → Canonical}
variable (leftOld : PointReadings leftData.anchors leftData.offsets leftPoints)
variable (rightOld : PointReadings rightData.anchors rightData.offsets rightPoints)
variable {ambient : Box}

/-- A retained segment bank keeps all actual Point, Entry, join, subdivision and comparison inputs together.

The endpoint equalities concern the SAME original numerical reading
positions. Both original Entry sheet laws merely reindex their unchanged
reachability proofs; the actual signed relation is the stored OwnerJoin.
-/
abbrev AtSegment {first last : Canonical} (segment : ClearSegment curve.polynomial ambient first last)
    (leftFirst leftLast : Fin leftSize) (rightFirst rightLast : Fin rightSize) :=
  Σ endpoints : {_value : Unit // leftPoints leftFirst = first ∧ leftPoints leftLast = last ∧
      rightPoints rightFirst = first ∧ rightPoints rightLast = last},
  Σ leftPoint : Entry.PointData (curve := curve) first,
  Σ rightPoint : Entry.PointData (curve := curve) first,
  Σ leftEntry : {value : Entry leftModels first leftPoint.sample.owner // value.sheet = leftSheet},
  Σ rightEntry : {value : Entry rightModels first rightPoint.sample.owner // value.sheet = rightSheet},
  Σ joined : OwnerJoin leftPoint.sample.owner rightPoint.sample.owner,
  Σ retained : Subdivision leftData rightData segment leftOld rightOld leftFirst leftLast rightFirst rightLast
      endpoints.property.1 endpoints.property.2.1 endpoints.property.2.2.1 endpoints.property.2.2.2,
  Σ request : AccuracyRequest,
    Acquisition (leftPoint := leftPoint) (rightPoint := rightPoint)
      (leftEntry := leftEntry.val.withSheet leftSheet leftEntry.property)
      (rightEntry := rightEntry.val.withSheet rightSheet rightEntry.property)
      (sourceJoin := joined) (retained := retained) request

namespace AtSegment

variable {leftOld rightOld} {first last : Canonical}
variable {segment : ClearSegment curve.polynomial ambient first last}
variable {leftFirst leftLast : Fin leftSize} {rightFirst rightLast : Fin rightSize}

/-- Retain a complete actual segment acquisition at its literal source and reading positions.

Only the existing tuple is packed. All original Point, Entry, join and
bank factories remain supplied materialized values; none is executed.
-/
@[expose] def ofAcquisition (leftFirst_eq : leftPoints leftFirst = first) (leftLast_eq : leftPoints leftLast = last)
    (rightFirst_eq : rightPoints rightFirst = first) (rightLast_eq : rightPoints rightLast = last)
    (leftPoint rightPoint : Entry.PointData (curve := curve) first)
    (leftEntry : Entry leftModels first leftPoint.sample.owner) (leftSame : leftEntry.sheet = leftSheet)
    (rightEntry : Entry rightModels first rightPoint.sample.owner) (rightSame : rightEntry.sheet = rightSheet)
    (joined : OwnerJoin leftPoint.sample.owner rightPoint.sample.owner)
    (subdivision : Subdivision leftData rightData segment leftOld rightOld leftFirst leftLast rightFirst rightLast
      leftFirst_eq leftLast_eq rightFirst_eq rightLast_eq)
    (request : AccuracyRequest)
    (acquired : Acquisition (leftPoint := leftPoint) (rightPoint := rightPoint)
      (leftEntry := leftEntry.withSheet leftSheet leftSame)
      (rightEntry := rightEntry.withSheet rightSheet rightSame)
      (sourceJoin := joined) (retained := subdivision) request) :
    AtSegment leftOld rightOld segment leftFirst leftLast rightFirst rightLast :=
  ⟨⟨(), leftFirst_eq, leftLast_eq, rightFirst_eq, rightLast_eq⟩, leftPoint, rightPoint,
    ⟨leftEntry, leftSame⟩, ⟨rightEntry, rightSame⟩, joined, subdivision, request, acquired⟩

variable (retained : AtSegment leftOld rightOld segment leftFirst leftLast rightFirst rightLast)

/-- Read the SAME original left Point, local patch, count and containment certificate. -/
abbrev leftPoint : Entry.PointData (curve := curve) first := retained.2.1

/-- Read the distinct original right Point preparation without replacing its Owner. -/
abbrev rightPoint : Entry.PointData (curve := curve) first := retained.2.2.1

/-- Read the complete original left Entry and its actual old-domain sheet certificate. -/
abbrev leftEntry : {value : Entry leftModels first retained.leftPoint.sample.owner // value.sheet = leftSheet} :=
  retained.2.2.2.1

/-- Read the independent right Entry and its original domain-sheet certificate. -/
abbrev rightEntry : {value : Entry rightModels first retained.rightPoint.sample.owner // value.sheet = rightSheet} :=
  retained.2.2.2.2.1

/-- Read the literal original source OwnerJoin belonging to these two retained Points. -/
abbrev joined : OwnerJoin retained.leftPoint.sample.owner retained.rightPoint.sample.owner := retained.2.2.2.2.2.1

/-- Read the exact whole original common-subdivision cache. -/
abbrev subdivision : Subdivision leftData rightData segment leftOld rightOld leftFirst leftLast rightFirst rightLast
    retained.1.property.1 retained.1.property.2.1 retained.1.property.2.2.1 retained.1.property.2.2.2 :=
  retained.2.2.2.2.2.2.1

/-- Read the actual old request, without changing its tolerance or upgrading its observations. -/
abbrev request : AccuracyRequest := retained.2.2.2.2.2.2.2.1

/-- Read the whole original acquisition, including its allocation and complete Point/bank factory equations. -/
abbrev acquisition : Acquisition (leftPoint := retained.leftPoint) (rightPoint := retained.rightPoint)
    (leftEntry := retained.leftEntry.val.withSheet leftSheet retained.leftEntry.property)
    (rightEntry := retained.rightEntry.val.withSheet rightSheet retained.rightEntry.property)
    (sourceJoin := retained.joined) (retained := retained.subdivision) retained.request := retained.2.2.2.2.2.2.2.2

/-- Read the SAME materialized Point/Entry/join bank of this literal segment occurrence. -/
abbrev continued : Points retained.leftPoint retained.rightPoint
    (retained.leftEntry.val.withSheet leftSheet retained.leftEntry.property)
    (retained.rightEntry.val.withSheet rightSheet retained.rightEntry.property)
    retained.joined retained.subdivision := retained.acquisition.continued

/-- Read the whole original ordered comparison bank, retaining every local payment branch. -/
abbrev compared : Bank (sourceJoin := retained.joined) retained.continued retained.request :=
  retained.acquisition.compared

/-- Read this segment's actual original signed increment discrepancy. -/
abbrev increment : Canonical := retained.compared.increment

/-- Read its computed original common-child allowance with its actual count. -/
abbrev charge : Rational := retained.compared.charge

/-- The original bank bounds this SAME segment discrepancy without any new acquisition. -/
theorem increment_le : Norm.Basic.normSq retained.increment ≤ retained.charge := retained.compared.increment_le

/-- The retained source increment is expressed in the exact original endpoint reading positions. -/
theorem increment_eq : retained.increment =
    (leftOld.values leftLast - leftOld.values leftFirst) -
      (rightOld.values rightLast - rightOld.values rightFirst) := retained.compared.increment_eq

/-- An unmet request retains its exact original child occurrence and complete unpaid comparison cache. -/
abbrev Pending := retained.compared.Pending

/-- Inspect the SAME stored local payment decisions; no numerical observation or comparison is rerun. -/
def pending : List retained.Pending := retained.compared.pending

section Original

variable {retained}
variable (leftFirst_eq : leftPoints leftFirst = first) (leftLast_eq : leftPoints leftLast = last)
variable (rightFirst_eq : rightPoints rightFirst = first) (rightLast_eq : rightPoints rightLast = last)
variable (leftSource rightSource : Entry.PointData (curve := curve) first)
variable (leftSourceEntry : Entry leftModels first leftSource.sample.owner)
variable (leftSame : leftSourceEntry.sheet = leftSheet)
variable (rightSourceEntry : Entry rightModels first rightSource.sample.owner)
variable (rightSame : rightSourceEntry.sheet = rightSheet)
variable (sourceJoin : OwnerJoin leftSource.sample.owner rightSource.sample.owner)
variable (preparedSplit : Subdivision leftData rightData segment leftOld rightOld
  leftFirst leftLast rightFirst rightLast
  leftFirst_eq leftLast_eq rightFirst_eq rightLast_eq)
variable (requested : AccuracyRequest)
variable (acquired : Acquisition (leftPoint := leftSource) (rightPoint := rightSource)
  (leftEntry := leftSourceEntry.withSheet leftSheet leftSame)
  (rightEntry := rightSourceEntry.withSheet rightSheet rightSame)
  (sourceJoin := sourceJoin) (retained := preparedSplit) requested)

/-- Packing the segment returns its SAME whole original acquisition and all allocation/factory caches. -/
theorem ofAcquisition_acquisition :
    (ofAcquisition leftFirst_eq leftLast_eq rightFirst_eq rightLast_eq leftSource rightSource
      leftSourceEntry leftSame rightSourceEntry rightSame sourceJoin preparedSplit requested acquired).acquisition =
        acquired := by rfl

end Original

end AtSegment

/-- Actual segment banks follow the SAME original clear path and share literal old endpoint indices.

An empty path requires equality of the two old reading indices themselves.
A stationary nonempty segment remains a cons occurrence with its complete
bank; equal coordinates never erase it or identify its root owners.
-/
@[expose] def PathReadings
    (leftOld : PointReadings leftData.anchors leftData.offsets leftPoints)
    (rightOld : PointReadings rightData.anchors rightData.offsets rightPoints) :
    {first last : Canonical} → ClearPath curve.polynomial ambient first last →
    Fin leftSize → Fin leftSize → Fin rightSize → Fin rightSize → Type 3
  | _, _, .nil _, leftFirst, leftLast, rightFirst, rightLast =>
      {_value : PUnit.{4} // leftFirst = leftLast ∧ rightFirst = rightLast}
  | _, _, .cons segment tail, leftFirst, leftLast, rightFirst, rightLast =>
      Σ leftMiddle : Fin leftSize, Σ rightMiddle : Fin rightSize,
        AtSegment leftOld rightOld segment leftFirst leftMiddle rightFirst rightMiddle ×
          PathReadings leftOld rightOld tail leftMiddle leftLast rightMiddle rightLast
termination_by structural _ _ path _ _ _ _ => path

namespace PathReadings

variable {leftOld rightOld}

/-- Retain an empty numerical word at the SAME two original reading positions. -/
def nil (point : Canonical) (left : Fin leftSize) (right : Fin rightSize) :
    PathReadings leftOld rightOld (ClearPath.nil (ambient := ambient) point) left left right right :=
  ⟨PUnit.unit, rfl, rfl⟩

/-- Prepend an already materialized segment bank and retain the exact ordered tail.

This constructor performs no acquisition. The original cache, all its
source Points and joins, and the complete remaining word are passed once.
-/
def cons {first middle last : Canonical} {segment : ClearSegment curve.polynomial ambient first middle}
    {tail : ClearPath curve.polynomial ambient middle last}
    {leftFirst leftMiddle leftLast : Fin leftSize} {rightFirst rightMiddle rightLast : Fin rightSize}
    (head : AtSegment leftOld rightOld segment leftFirst leftMiddle rightFirst rightMiddle)
    (remaining : PathReadings leftOld rightOld tail leftMiddle leftLast rightMiddle rightLast) :
    PathReadings leftOld rightOld (.cons segment tail) leftFirst leftLast rightFirst rightLast :=
  ⟨leftMiddle, rightMiddle, head, remaining⟩

/-- The opaque prepend constructor retains its exact whole original head and tail tuple. -/
theorem cons_eq {first middle last : Canonical} {segment : ClearSegment curve.polynomial ambient first middle}
    {tail : ClearPath curve.polynomial ambient middle last}
    {leftFirst leftMiddle leftLast : Fin leftSize} {rightFirst rightMiddle rightLast : Fin rightSize}
    (head : AtSegment leftOld rightOld segment leftFirst leftMiddle rightFirst rightMiddle)
    (remaining : PathReadings leftOld rightOld tail leftMiddle leftLast rightMiddle rightLast) :
    cons head remaining = ⟨leftMiddle, rightMiddle, head, remaining⟩ := by rfl

/-- Read every literal signed segment discrepancy in original order, without coordinate deduplication. -/
def increments : {first last : Canonical} → {path : ClearPath curve.polynomial ambient first last} →
    {leftFirst leftLast : Fin leftSize} → {rightFirst rightLast : Fin rightSize} →
    PathReadings leftOld rightOld path leftFirst leftLast rightFirst rightLast → List Canonical
  | _, _, .nil _, _, _, _, _, _ => []
  | _, _, .cons _ _, _, _, _, _, retained => retained.2.2.1.increment :: increments retained.2.2.2
termination_by structural _ _ path _ _ _ _ _ => path

/-- Read the matching original segment allowances, preserving every repeated or stationary occurrence. -/
def charges : {first last : Canonical} → {path : ClearPath curve.polynomial ambient first last} →
    {leftFirst leftLast : Fin leftSize} → {rightFirst rightLast : Fin rightSize} →
    PathReadings leftOld rightOld path leftFirst leftLast rightFirst rightLast → List Rational
  | _, _, .nil _, _, _, _, _, _ => []
  | _, _, .cons _ _, _, _, _, _, retained => retained.2.2.1.charge :: charges retained.2.2.2
termination_by structural _ _ path _ _ _ _ _ => path

/-- Each original word position retains its own typed unpaid child data.

The nested sum is the exact original head/tail occurrence route. Neither
coordinates nor matching labels are used to merge requests.
-/
@[expose] def Pending : {first last : Canonical} → {path : ClearPath curve.polynomial ambient first last} →
    {leftFirst leftLast : Fin leftSize} → {rightFirst rightLast : Fin rightSize} →
    (retained : PathReadings leftOld rightOld path leftFirst leftLast rightFirst rightLast) → Type 3
  | _, _, .nil _, _, _, _, _, _ => PEmpty.{4}
  | _, _, .cons _ _, _, _, _, _, retained => retained.2.2.1.Pending ⊕ Pending retained.2.2.2
termination_by structural _ _ path _ _ _ _ _ => path

/-- Preserve all actual unpaid requests in original segment/child order.

Only finite request metadata is traversed. Nested tail injections can copy
metadata prefixes; they never acquire or replay the old child caches.
-/
def pending : {first last : Canonical} → {path : ClearPath curve.polynomial ambient first last} →
    {leftFirst leftLast : Fin leftSize} → {rightFirst rightLast : Fin rightSize} →
    (retained : PathReadings leftOld rightOld path leftFirst leftLast rightFirst rightLast) → List retained.Pending
  | _, _, .nil _, _, _, _, _, _ => []
  | _, _, .cons _ _, _, _, _, _, retained =>
      (retained.2.2.1.pending.map Sum.inl) ++ (pending retained.2.2.2).map Sum.inr
termination_by structural _ _ path _ _ _ _ _ => path

variable {first last : Canonical} {path : ClearPath curve.polynomial ambient first last}
variable {leftFirst leftLast : Fin leftSize} {rightFirst rightLast : Fin rightSize}
variable (retained : PathReadings leftOld rightOld path leftFirst leftLast rightFirst rightLast)

/-- The actual segment count includes stationary and repeated original occurrences. -/
theorem increments_length : retained.increments.length = path.segmentCount := by
  induction path generalizing leftFirst leftLast rightFirst rightLast with
  | nil point => rfl
  | cons segment tail previous =>
      exact congrArg (fun count => count + 1) (previous retained.2.2.2)

/-- The ordered segment discrepancies telescope only at the SAME retained old numerical positions.

The independent left and right constants are never identified. Partial,
reverse and repeated segments use their actual original endpoint indices.
-/
theorem increment_eq : Norm.Sum.Basic.gaussianSum retained.increments =
    (leftOld.values leftLast - leftOld.values leftFirst) -
      (rightOld.values rightLast - rightOld.values rightFirst) := by
  induction path generalizing leftFirst leftLast rightFirst rightLast with
  | nil point =>
      have left := retained.property.1
      have right := retained.property.2
      cases left
      cases right
      change (0 : Canonical) = (_ - _) - (_ - _)
      ring1
  | cons segment tail previous =>
      change retained.2.2.1.increment + Norm.Sum.Basic.gaussianSum retained.2.2.2.increments = _
      rewrite [retained.2.2.1.increment_eq, previous retained.2.2.2]
      ring1

/-- The actual squared discrepancies sum below the matching old segment allowances. -/
theorem norm_sum_le : Norm.Sum.Basic.gaussianNormSqSum retained.increments ≤ coordinateSum retained.charges := by
  induction path generalizing leftFirst leftLast rightFirst rightLast with
  | nil point => exact Order.Basic.le_refl 0
  | cons segment tail previous =>
      change Canonical.normSq retained.2.2.1.increment +
        Norm.Sum.Basic.gaussianNormSqSum retained.2.2.2.increments ≤
        retained.2.2.1.charge + coordinateSum retained.2.2.2.charges
      have head := retained.2.2.1.increment_le
      rewrite [Norm.Basic.normSq_eq_canonical] at head
      exact Order.Arithmetic.add_le_add_direct head (previous retained.2.2.2)

/-- Compute the actual whole-word discrepancy on the retained segment bank. -/
def increment : Canonical := Norm.Sum.Basic.gaussianSum retained.increments

/-- The whole-word charge uses the literal original segment count and all actual segment charges. -/
def charge : Rational := Aggregate.countCoordinate path.segmentCount * coordinateSum retained.charges

/-- Finite Cauchy pays the actual whole-word discrepancy from the retained original segment allowances. -/
theorem increment_le : Norm.Basic.normSq retained.increment ≤ retained.charge := by
  have summed := Norm.Sum.Basic.normSq_gaussianSum_le retained.increments
  rewrite [retained.increments_length] at summed
  have dominated := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct retained.norm_sum_le
    (Order.NatCast.qNatNonnegative path.segmentCount)
  change Norm.Basic.normSq (Norm.Sum.Basic.gaussianSum retained.increments) ≤
    Aggregate.countCoordinate path.segmentCount * coordinateSum retained.charges
  rewrite [Norm.Basic.normSq_eq_canonical, Aggregate.countCoordinate_eq]
  exact summed.trans dominated

/-- Both complete original primitive increments satisfy the actual aggregate allowance. -/
theorem source_increment_le : Norm.Basic.normSq
    ((leftOld.values leftLast - leftOld.values leftFirst) -
      (rightOld.values rightLast - rightOld.values rightFirst)) ≤ retained.charge :=
  Eq.mp (congrArg (fun value => Norm.Basic.normSq value ≤ retained.charge) retained.increment_eq)
    retained.increment_le

/-- A finite payment keeps the whole original word and all actual aggregate summaries and local requests. -/
abbrev Payment (request : AccuracyRequest) :=
  {value : PathReadings leftOld rightOld path leftFirst leftLast rightFirst rightLast // value = retained} ×
  (Σ _increment : {value : Canonical // value = retained.increment},
  Σ charge : {value : Rational // value = retained.charge},
  Σ _pending : {value : List retained.Pending // value = retained.pending},
    {_value : Unit // charge.val < request.tolerance} ⊕
      {_value : Unit // ¬charge.val < request.tolerance})

/-- Compute the actual finite word summaries once and retain a successful or unresolved whole-payment decision.

All old requests and observations keep their original tolerances. A
negative decision retains the whole attempted word, its computed count
charge and every unmet child request; no old accuracy is upgraded.
-/
def pay (request : AccuracyRequest) : retained.Payment request :=
  let increment := retained.increment
  let total := retained.charge
  let unmet := retained.pending
  if sufficient : total < request.tolerance then
    (⟨retained, rfl⟩, ⟨⟨increment, rfl⟩, ⟨total, rfl⟩, ⟨unmet, rfl⟩, Sum.inl ⟨(), sufficient⟩⟩)
  else
    (⟨retained, rfl⟩, ⟨⟨increment, rfl⟩, ⟨total, rfl⟩, ⟨unmet, rfl⟩, Sum.inr ⟨(), sufficient⟩⟩)

namespace Payment

variable {retained} {request : AccuracyRequest} (paid : retained.Payment request)

/-- Read the SAME whole original ordered segment banks. -/
abbrev original : PathReadings leftOld rightOld path leftFirst leftLast rightFirst rightLast := paid.1.val

/-- Read the cached actual whole-word discrepancy. -/
abbrev increment : Canonical := paid.2.1.val

/-- Read the exact aggregate allowance used by this finite decision. -/
abbrev charge : Rational := paid.2.2.1.val

/-- Read every retained original unpaid segment/child request with its exact occurrence route. -/
abbrev pending : List retained.Pending := paid.2.2.2.1.val

/-- Read the positive or negative actual charge certificate; neither branch changes an old request. -/
abbrev decision : {_value : Unit // paid.charge < request.tolerance} ⊕
    {_value : Unit // ¬paid.charge < request.tolerance} := paid.2.2.2.2

/-- The original complete word remains whole-value equal to its actual supplied cache. -/
theorem original_eq : paid.original = retained := paid.1.property

/-- The cached discrepancy retains its exact original ordered finite-sum expression. -/
theorem increment_eq : paid.increment = retained.increment := paid.2.1.property

/-- The exact aggregate allowance is its original computed count-and-charge expression. -/
theorem charge_eq : paid.charge = retained.charge := paid.2.2.1.property

/-- All retained actual unpaid children remain linked to the original finite inspection. -/
theorem pending_eq : paid.pending = retained.pending := paid.2.2.2.1.property

/-- Actual finite success pays the SAME two old whole-word primitive increments. -/
theorem accurate (sufficient : paid.charge < request.tolerance) : Norm.Basic.normSq
    ((leftOld.values leftLast - leftOld.values leftFirst) -
      (rightOld.values rightLast - rightOld.values rightFirst)) < request.tolerance :=
  (retained.source_increment_le.trans_eq paid.charge_eq.symm).trans_lt sufficient

end Payment

end PathReadings

end Bank

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives.Junction.Subdivision

end
