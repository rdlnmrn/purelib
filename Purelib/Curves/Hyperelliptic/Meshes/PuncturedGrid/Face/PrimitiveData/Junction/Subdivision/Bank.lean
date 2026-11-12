module

import Init.Data.Sum.Basic
import Init.Data.Option.Basic
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.Junction.Subdivision.Points
public import Purelib.Approximation.AccuracyRequest
public import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Gaussian.Field
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Ordered retained common-child comparisons and actual finite payments

Each child consumes the same materialized common Point bank. Its original
preparation/payment attempt is retained, and the derived source sheets
exclude missing or mismatched preparation. Actual primitive allowances
sum with the real child count; unpaid local requests stay inspectable.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives.Junction.Subdivision

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Vector (DependentVector)
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational.Budget
open Purelib.Data.Gaussian
open Purelib.Data.List
open Purelib.Geometry.Rational (Box)
open Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions (Interval)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Paths.OwnerTraceReadings (OwnerJoin)
open Purelib.Riemann.Paths.RectangularSegmentSplitting
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {frames : RootFrames bank.grid} {leftFace rightFace : RegularFace bank}
variable {leftModels : FaceModels frames leftFace} {rightModels : FaceModels frames rightFace}
variable {first last : Canonical}
variable (leftPoint rightPoint : Entry.PointData (curve := curve) first)
variable (leftEntry : Entry leftModels first leftPoint.sample.owner)
variable (rightEntry : Entry rightModels first rightPoint.sample.owner)
variable (sourceJoin : OwnerJoin leftPoint.sample.owner rightPoint.sample.owner)
variable {leftDomain : PeriodDomain leftModels leftEntry.sheet}
variable {rightDomain : PeriodDomain rightModels rightEntry.sheet}
variable {differential : Differential genus} {leftIndex rightIndex : Nat}
variable {leftData : DomainPrimitives leftDomain differential leftIndex}
variable {rightData : DomainPrimitives rightDomain differential rightIndex}
variable {ambient : Box} {source : ClearSegment curve.polynomial ambient first last}
variable {leftSize rightSize : Nat} {leftPoints : Fin leftSize → Canonical} {rightPoints : Fin rightSize → Canonical}
variable {leftOld : PointReadings leftData.anchors leftData.offsets leftPoints}
variable {rightOld : PointReadings rightData.anchors rightData.offsets rightPoints}
variable {leftFirst leftLast : Fin leftSize} {rightFirst rightLast : Fin rightSize}
variable {leftFirst_eq : leftPoints leftFirst = first} {leftLast_eq : leftPoints leftLast = last}
variable {rightFirst_eq : rightPoints rightFirst = first} {rightLast_eq : rightPoints rightLast = last}
variable (retained : Subdivision leftData rightData source leftOld rightOld leftFirst leftLast rightFirst rightLast
  leftFirst_eq leftLast_eq rightFirst_eq rightLast_eq)

variable {leftPoint rightPoint leftEntry rightEntry sourceJoin retained}
variable (points : Points leftPoint rightPoint leftEntry rightEntry sourceJoin retained)

section Child

variable {child : CommonChild leftDomain.cuts rightDomain.cuts first last retained.common.partition}
variable {allowance : Rational} {cell : Cell retained child}

namespace Points.ChildAttempt

variable (attempted : points.ChildAttempt cell allowance)

/-- Read the exact whole constructed child preparation used by the original attempt. -/
abbrev lower : Cell.LowerData cell := attempted.1.val

/-- Read the complete original attempt, preserving its actual finite payment branch. -/
abbrev result : cell.Attempt (some attempted.lower) allowance := attempted.2.val

/-- The exact original constructed lower cache retains its complete factory equality. -/
theorem lower_eq : attempted.lower = points.forCell cell := attempted.1.property

/-- The actual attempt uses the original left domain sheet derived from the source Entry. -/
theorem left_sheet : attempted.lower.leftAcquired.entry.sheet = leftEntry.sheet :=
  (congrArg (fun value : Cell.LowerData cell => value.leftAcquired.entry.sheet) attempted.lower_eq).trans
    (points.forCell_left_sheet cell)

/-- The same attempt preserves the distinct original right domain sheet. -/
theorem right_sheet : attempted.lower.rightAcquired.entry.sheet = rightEntry.sheet :=
  (congrArg (fun value : Cell.LowerData cell => value.rightAcquired.entry.sheet) attempted.lower_eq).trans
    (points.forCell_right_sheet cell)

/-- The original successful preparation branch retains its actual Ready and payment caches.

This is exactly the existing attempt's inner Sigma container. Its numerical
payment can still be unpaid; success here means only genuine preparation
and the original two sheet checks.
-/
abbrev Prepared :=
  Σ actual : {value : Cell.LowerData cell // some attempted.lower = some value},
    Cell.Prepared (leftModels := leftModels) (rightModels := rightModels)
      (leftSheet := leftEntry.sheet) (rightSheet := rightEntry.sheet) cell actual.val allowance

/-- Read the actual preparation branch, excluding only impossible missing-cache or sheet-mismatch branches.

Both exclusions follow from the supplied actual attempt cache and the
source-derived sheet laws above. The original Ready and numerical Payment
values are returned directly; no comparison or observation is acquired.
-/
def prepared : attempted.Prepared :=
  Cell.Attempt.prepared (leftModels := leftModels) (rightModels := rightModels)
    (leftSheet := leftEntry.sheet) (rightSheet := rightEntry.sheet) cell attempted.lower allowance
    attempted.result attempted.left_sheet attempted.right_sheet

namespace Prepared

variable {points attempted} (prepared : attempted.Prepared)

/-- Read the actual unchanged primitive comparison and computed ownership charges. -/
abbrev ready : Cell.Ready cell prepared.1.val prepared.2.1.property.1 prepared.2.1.property.2 :=
  Cell.Prepared.ready prepared.2

/-- Read the complete original finite endpoint-error payment at its actual remaining allowance. -/
abbrev payment : prepared.ready.Payment allowance := Cell.Prepared.payment prepared.2

/-- An unmet local request retains the complete existing prepared branch and exact failed remaining-error demand. -/
@[expose] def Unpaid : Type _ :=
  Σ actual : {value : attempted.Prepared // value = prepared},
    {_value : Unit // ¬actual.val.ready.errors.bound < actual.val.ready.remaining allowance}

/-- Return the exact original unpaid payment, or no request when that SAME cached payment succeeded.

The comparison is inspected, not rerun. Its negative certificate concerns
only the actual old stages and the requested remaining allowance.
-/
def unpaid : Option prepared.Unpaid :=
  prepared.payment.val.2.getRight?.map fun missing => ⟨⟨prepared, rfl⟩, missing⟩

end Prepared

end Points.ChildAttempt

end Child

namespace Bank

/-- Read one literal ordered child from the SAME retained common subdivision. -/
abbrev child (position : Fin retained.common.children.length) :
    CommonChild leftDomain.cuts rightDomain.cuts first last retained.common.partition :=
  retained.common.children[position.val]'position.isLt

/-- One occurrence retains its original cell observation, full attempt and actual prepared/payment branch. -/
abbrev Item (child : CommonChild leftDomain.cuts rightDomain.cuts first last retained.common.partition)
    (allowance : Rational) :=
  Σ cell : {value : Cell retained child // value = observeChild retained child},
  Σ attempted : {value : points.ChildAttempt cell.val allowance //
      value = points.attemptCell cell.val allowance},
    {value : attempted.val.Prepared // value = attempted.val.prepared}

namespace Item

/-- Materialize one real child comparison, then retain the existing attempt's prepared branch without replay. -/
def build (child : CommonChild leftDomain.cuts rightDomain.cuts first last retained.common.partition)
    (allowance : Rational) : Item points child allowance :=
  let cell := observeChild retained child
  let attempted := points.attemptCell cell allowance
  let prepared := attempted.prepared
  ⟨⟨cell, rfl⟩, ⟨attempted, rfl⟩, ⟨prepared, rfl⟩⟩

variable {points} {selected : CommonChild leftDomain.cuts rightDomain.cuts first last retained.common.partition}
variable {allowance : Rational} (item : Item points selected allowance)

/-- Read the actual midpoint cells, both independent reading banks and cached endpoint positions. -/
abbrev cell : Cell retained selected := item.1.val

/-- Read the SAME whole original child attempt and all of its numerical data. -/
abbrev attempted : points.ChildAttempt item.cell allowance := item.2.1.val

/-- Read the exact derived preparation branch, including the actual original finite payment. -/
abbrev prepared : item.attempted.Prepared := item.2.2.val

/-- Read the unchanged primitive/model/ownership comparison bound of this actual signed child. -/
abbrev charge : Rational := item.prepared.ready.bound

/-- The signed policy increment difference keeps both independent original offsets and endpoint occurrences. -/
def increment : Canonical :=
  (retained.left.readings.values item.cell.upper.val.index -
    retained.left.readings.values item.cell.lower.val.index) -
  (retained.right.readings.values item.cell.upper.val.index -
    retained.right.readings.values item.cell.lower.val.index)

/-- Each actual signed increment is bounded by its retained original Ready allowance. -/
theorem increment_le : Norm.Basic.normSq item.increment ≤ item.charge :=
  item.prepared.ready.policy_increment_le

end Item

end Bank

/-- An ordered bank retains its global request, preallocated child allowance and all original attempts.

The common Point bank is an input retained unchanged. The local allowance
is computed before any new child midpoint evaluation, primitive comparison
or payment, using the literal current common-child count.
-/
abbrev Bank (request : AccuracyRequest) :=
  {value : Points leftPoint rightPoint leftEntry rightEntry sourceJoin retained × AccuracyRequest //
    value = (points, request)} ×
  (Σ allowance : {value : Rational // value = Aggregate.perTerm request.tolerance retained.common.count},
    {value : DependentVector (fun position : Fin retained.common.children.length =>
        Bank.Item points (Bank.child (retained := retained) position) allowance.val) //
      value = DependentVector.ofFn (fun position =>
        Bank.Item.build points (Bank.child (retained := retained) position) allowance.val)})

namespace Bank

/-- Consume a retained original count allocation and materialize each ordered child attempt once. -/
def ofAllowance (request : AccuracyRequest) (allowance : Rational)
    (same : allowance = Aggregate.perTerm request.tolerance retained.common.count) : Bank points request :=
  let items := DependentVector.ofFn fun position => Item.build points (child (retained := retained) position) allowance
  (⟨(points, request), rfl⟩, ⟨⟨allowance, same⟩, ⟨items, rfl⟩⟩)

/-- Allocate before child work, then materialize each ordered cell/attempt exactly once. -/
def build (request : AccuracyRequest) : Bank points request :=
  let allowance := Aggregate.perTerm request.tolerance retained.common.count
  ofAllowance points request allowance rfl

/-- A source-owned acquisition retains its allocation before the new common Point and child comparison work. -/
abbrev Acquisition (request : AccuracyRequest) :=
  Σ allowance : {value : Rational // value = Aggregate.perTerm request.tolerance retained.common.count},
  Σ points : {value : Points leftPoint rightPoint leftEntry rightEntry sourceJoin retained //
      value = Points.build leftPoint rightPoint leftEntry rightEntry sourceJoin retained},
    {value : Bank (sourceJoin := sourceJoin) points.val request //
      value = ofAllowance (sourceJoin := sourceJoin) points.val request allowance.val allowance.property}

/-- Compute the actual count allowance before acquiring any new common Point or child comparison. -/
def acquire (request : AccuracyRequest) : Acquisition (sourceJoin := sourceJoin) (retained := retained) request :=
  let allowance := Aggregate.perTerm request.tolerance retained.common.count
  let points := Points.build leftPoint rightPoint leftEntry rightEntry sourceJoin retained
  let compared := ofAllowance (sourceJoin := sourceJoin) points request allowance rfl
  ⟨⟨allowance, rfl⟩, ⟨points, rfl⟩, ⟨compared, rfl⟩⟩

namespace Acquisition

variable {request : AccuracyRequest} (acquired : Acquisition (sourceJoin := sourceJoin) (retained := retained) request)

/-- Read the actual allocation computed before all new common Point and child work. -/
abbrev allocation : Rational := acquired.1.val

/-- Read the SAME materialized common Point/Entry/join bank built by this source-owned acquisition. -/
abbrev continued : Points leftPoint rightPoint leftEntry rightEntry sourceJoin retained := acquired.2.1.val

/-- Read the whole actual ordered child comparison bank, using that SAME Point bank and allocation. -/
abbrev compared : Bank (sourceJoin := sourceJoin) acquired.continued request := acquired.2.2.val

/-- The retained allocation keeps the original aggregate constructor at the actual cached child count. -/
theorem allocation_eq : acquired.allocation = Aggregate.perTerm request.tolerance retained.common.count :=
  acquired.1.property

/-- The materialized Point bank retains its complete original construction equation. -/
theorem continued_eq : acquired.continued =
    Points.build leftPoint rightPoint leftEntry rightEntry sourceJoin retained := acquired.2.1.property

/-- The actual comparison bank consumes the SAME prior allocation without recomputing it. -/
theorem compared_eq : acquired.compared =
    ofAllowance (sourceJoin := sourceJoin) acquired.continued request acquired.allocation acquired.allocation_eq :=
  acquired.2.2.property

end Acquisition

variable {points} {request : AccuracyRequest} (collected : Bank points request)

/-- Read the actual count-adjusted local request selected before the child comparison factories. -/
abbrev allowance : Rational := collected.2.1.val

/-- Read the original retained dependent spine of actual child comparisons and payments. -/
abbrev items : DependentVector (fun position : Fin retained.common.children.length =>
    Item points (child (retained := retained) position) collected.allowance) := collected.2.2.val

/-- Read the SAME ordered cached child occurrence without acquiring any Point, Entry, join or primitive observation. -/
abbrev item (position : Fin retained.common.children.length) :
    Item points (child (retained := retained) position) collected.allowance := collected.items.get position

/-- The cached local request is the original aggregate count allocation. -/
theorem allowance_eq : collected.allowance = Aggregate.perTerm request.tolerance retained.common.count :=
  collected.2.1.property

/-- Every actual child request is positive, including for stationary sources. -/
theorem allowance_positive : 0 < collected.allowance :=
  (Aggregate.perTerm_positive request.positive retained.common.count).trans_eq collected.allowance_eq.symm

/-- The whole ordered item spine retains its complete original materialization factory. -/
theorem items_eq : collected.items = DependentVector.ofFn (fun position =>
    Item.build points (child (retained := retained) position) collected.allowance) := collected.2.2.property

/-- The whole signed increment discrepancy sums the literal ordered common-child occurrences. -/
def increment : Canonical := sumFin (fun position => (collected.item position).increment)

/-- The computed whole-segment allowance uses the actual count and all retained primitive/ownership charges. -/
def charge : Rational := Aggregate.countCoordinate retained.common.count *
  sumFin (fun position => (collected.item position).charge)

/-- Finite Cauchy summation bounds the actual whole signed increment by its computed allowance. -/
theorem increment_le : Norm.Basic.normSq collected.increment ≤ collected.charge := by
  have estimate := Norm.Sum.Indexed.normSq_sumFin_le_count_mul_sumFin
    (fun position => (collected.item position).increment) (fun position => (collected.item position).charge)
    (fun position => (collected.item position).increment_le)
  have sameCount : Aggregate.countCoordinate retained.common.count =
      (retained.common.children.length : Rational) :=
    (Aggregate.countCoordinate_eq retained.common.count).trans
      (congrArg (fun count : Nat => (count : Rational)) retained.common.count_eq)
  exact estimate.trans_eq
    (congrArg (fun count : Rational =>
      count * sumFin (fun position => (collected.item position).charge)) sameCount.symm)

/-- A proof-local scalar lookup reads only the original coordinate selection and retained reading vector. -/
private def policy (values : Fin retained.common.partition.coordinates.length → Canonical) (parameter : Rational) :
    Canonical :=
  match Search.firstOccurrence (fun value : Rational => value = parameter) (fun _ => inferInstance)
      retained.common.partition.coordinates with
  | none => 0
  | some selected => values selected.index

/-- Actual cached first-occurrence evidence reduces the proof-local lookup to that SAME retained scalar. -/
private theorem policy_eq (values : Fin retained.common.partition.coordinates.length → Canonical)
    {parameter : Rational}
    (selected : Position (leftDomain := leftDomain) (rightDomain := rightDomain) retained.common parameter) :
    policy (retained := retained) values parameter = values selected.val.index := by
  unfold policy
  exact congrArg
    (fun found : Option (Search.Occurrence (fun value : Rational => value = parameter)
      retained.common.partition.coordinates) =>
      match found with
      | none => 0
      | some entry => values entry.index) selected.property

/-- The proof-local difference retains both independent primitive constants and lookup policies. -/
private def gap (parameter : Rational) : Canonical :=
  policy (retained := retained) retained.left.readings.values parameter -
    policy (retained := retained) retained.right.readings.values parameter

/-- Read the literal original child interval without changing either endpoint reading owner. -/
private theorem item_increment_eq (position : Fin retained.common.children.length) :
    (collected.item position).increment =
      gap (retained := retained) (child (retained := retained) position).1.val.upper -
        gap (retained := retained) (child (retained := retained) position).1.val.lower := by
  have leftUpper := policy_eq (retained := retained) retained.left.readings.values (collected.item position).cell.upper
  have leftLower := policy_eq (retained := retained) retained.left.readings.values (collected.item position).cell.lower
  have rightUpper := policy_eq (retained := retained) retained.right.readings.values
    (collected.item position).cell.upper
  have rightLower := policy_eq (retained := retained) retained.right.readings.values
    (collected.item position).cell.lower
  dsimp only [Item.increment, gap]
  rw [leftUpper, leftLower, rightUpper, rightLower]
  ring1

/-- The old zero-parameter observation is retained exactly in the proof-local left reading. -/
private theorem left_zero :
    policy (retained := retained) retained.left.readings.values 0 = leftOld.values leftFirst := by
  let selected := position (leftDomain := leftDomain) (rightDomain := rightDomain) retained.common 0
    retained.common.partition.lower_mem
  exact (policy_eq (retained := retained) retained.left.readings.values selected).trans
    (retained.left.value_at_zero selected.val.index
      (position_eq (leftDomain := leftDomain) (rightDomain := rightDomain) selected))

/-- The old one-parameter observation stays distinct in the proof-local left reading. -/
private theorem left_one :
    policy (retained := retained) retained.left.readings.values 1 = leftOld.values leftLast := by
  let selected := position (leftDomain := leftDomain) (rightDomain := rightDomain) retained.common 1
    retained.common.partition.upper_mem
  exact (policy_eq (retained := retained) retained.left.readings.values selected).trans
    (retained.left.value_at_one selected.val.index
      (position_eq (leftDomain := leftDomain) (rightDomain := rightDomain) selected))

/-- The independent original right lower observation is retained without offset normalization. -/
private theorem right_zero :
    policy (retained := retained) retained.right.readings.values 0 = rightOld.values rightFirst := by
  let selected := position (leftDomain := leftDomain) (rightDomain := rightDomain) retained.common 0
    retained.common.partition.lower_mem
  exact (policy_eq (retained := retained) retained.right.readings.values selected).trans
    (retained.right.value_at_zero selected.val.index
      (position_eq (leftDomain := leftDomain) (rightDomain := rightDomain) selected))

/-- The independent original right upper observation keeps its own original owner and scalar. -/
private theorem right_one :
    policy (retained := retained) retained.right.readings.values 1 = rightOld.values rightLast := by
  let selected := position (leftDomain := leftDomain) (rightDomain := rightDomain) retained.common 1
    retained.common.partition.upper_mem
  exact (policy_eq (retained := retained) retained.right.readings.values selected).trans
    (retained.right.value_at_one selected.val.index
      (position_eq (leftDomain := leftDomain) (rightDomain := rightDomain) selected))

/-- The actual ordered child discrepancy telescopes to both original retained endpoint increments.

Only shared parameter positions in the SAME two numerical reading banks
cancel. The two domains' constants, offsets, endpoint owners and repeated
physical occurrences are never identified with one another.
-/
theorem increment_eq : collected.increment =
    (leftOld.values leftLast - leftOld.values leftFirst) -
      (rightOld.values rightLast - rightOld.values rightFirst) := by
  let intervalValue := fun interval : Interval =>
    gap (retained := retained) interval.upper - gap (retained := retained) interval.lower
  have terms := OfFn.Basic.ofFn_congr (fun position => collected.item_increment_eq position)
  have enumeration :
      List.ofFn (fun position : Fin retained.common.children.length =>
        intervalValue (child (retained := retained) position).1.val) =
        retained.common.children.map (fun child => intervalValue child.1.val) := by
    have mapped := OfFn.Basic.map_ofFn
      (function := fun position : Fin retained.common.children.length =>
        retained.common.children[position.val]'position.isLt)
      (transform := fun child => intervalValue child.1.val)
    rw [OfFn.Basic.ofFn_getElem] at mapped
    exact mapped.symm
  have nested : retained.common.children.map (fun child => intervalValue child.1.val) =
      (retained.common.children.map (fun child => child.1.val)).map intervalValue :=
    (Data.List.Map.map_map
      (Alpha := CommonChild leftDomain.cuts rightDomain.cuts first last retained.common.partition)
      (Beta := Interval) (Gamma := Canonical) intervalValue (fun child => child.1.val)
      retained.common.children).symm
  have telescope := SegmentSplit.intervals_telescope (gap (retained := retained)) retained.common.partition.walk
  rw [retained.common.partition.walk_edges] at telescope
  have total : collected.increment = gap (retained := retained) 1 - gap (retained := retained) 0 := by
    unfold increment
    rw [Norm.Sum.Indexed.sumFin_eq_gaussianSum, terms, enumeration, nested, retained.common.intervals_eq]
    exact telescope
  rw [total]
  dsimp only [gap]
  rw [left_one (retained := retained), left_zero (retained := retained),
    right_one (retained := retained), right_zero (retained := retained)]
  ring1

/-- The two actual old-domain source increments satisfy the derived full common-child allowance. -/
theorem source_increment_le : Norm.Basic.normSq
    ((leftOld.values leftLast - leftOld.values leftFirst) -
      (rightOld.values rightLast - rightOld.values rightFirst)) ≤ collected.charge :=
  Eq.mp (congrArg (fun value => Norm.Basic.normSq value ≤ collected.charge) collected.increment_eq)
    collected.increment_le

/-- Opposite boundary signs use the same observations and charge without reversing any Owner or path. -/
theorem opposite_increment_le : Norm.Basic.normSq
    ((leftOld.values leftLast - leftOld.values leftFirst) +
      (rightOld.values rightFirst - rightOld.values rightLast)) ≤ collected.charge := by
  have scalar : (leftOld.values leftLast - leftOld.values leftFirst) +
      (rightOld.values rightFirst - rightOld.values rightLast) =
      (leftOld.values leftLast - leftOld.values leftFirst) -
        (rightOld.values rightLast - rightOld.values rightFirst) := by ring1
  rw [scalar]
  exact collected.source_increment_le

/-- One actual unpaid child keeps its ordered position and the whole original failed payment data. -/
abbrev Pending := Σ position : Fin retained.common.children.length, (collected.item position).prepared.Unpaid

/-- Inspect the retained original local payments in order, preserving every unmet occurrence. -/
private def collectPending : List (Fin retained.common.children.length) → List collected.Pending
  | [] => []
  | position :: remaining =>
    match (collected.item position).prepared.unpaid with
    | none => collectPending remaining
    | some unmet => ⟨position, unmet⟩ :: collectPending remaining

/-- Return every actual unresolved local payment in original bounded-index order.

Each returned value contains the exact prepared comparison, both old
reading owners and failed remaining allowance. A local failure is not a
geometric obstruction or a global divergence claim.
-/
def pending : List collected.Pending := collectPending collected (List.ofFn id)

/-- A whole payment retains its actual summed discrepancy, charge, unmet local data and finite decision. -/
abbrev Payment :=
  {value : Bank points request // value = collected} ×
  (Σ _increment : {value : Canonical // value = collected.increment},
  Σ charge : {value : Rational // value = collected.charge},
  Σ _pending : {value : List collected.Pending // value = collected.pending},
    {_value : Unit // charge.val < request.tolerance} ⊕
      {_value : Unit // ¬charge.val < request.tolerance})

/-- Compute the two whole summaries once and check their actual allowance, preserving every old observation. -/
def pay : collected.Payment :=
  let increment := collected.increment
  let total := collected.charge
  let unmet := collected.pending
  if paid : total < request.tolerance then
    (⟨collected, rfl⟩, ⟨⟨increment, rfl⟩, ⟨total, rfl⟩, ⟨unmet, rfl⟩, Sum.inl ⟨(), paid⟩⟩)
  else (⟨collected, rfl⟩, ⟨⟨increment, rfl⟩, ⟨total, rfl⟩, ⟨unmet, rfl⟩, Sum.inr ⟨(), paid⟩⟩)

namespace Payment

variable {collected} (paid : collected.Payment)

/-- Read the actual once-summed ordered discrepancy. -/
abbrev increment : Canonical := paid.2.1.val

/-- Read the same computed whole primitive/ownership allowance used by the finite decision. -/
abbrev charge : Rational := paid.2.2.1.val

/-- Read every exact unmet local request with its original child/cache owner. -/
abbrev pending : List collected.Pending := paid.2.2.2.1.val

/-- Read the actual retained whole-charge decision and its positive or negative scalar certificate. -/
abbrev decision : {_value : Unit // paid.charge < request.tolerance} ⊕
    {_value : Unit // ¬paid.charge < request.tolerance} := paid.2.2.2.2

/-- The cached unmet child list retains the complete original finite inspection factory. -/
theorem pending_eq : paid.pending = collected.pending := paid.2.2.2.1.property

/-- The cached discrepancy keeps its complete original finite-sum factory. -/
theorem increment_eq : paid.increment = collected.increment := paid.2.1.property

/-- The cached charge retains the exact original ordered sum of actual Ready allowances. -/
theorem charge_eq : paid.charge = collected.charge := paid.2.2.1.property

/-- The retained original endpoint increments are bounded by the SAME cached charge. -/
theorem source_increment_le : Norm.Basic.normSq
    ((leftOld.values leftLast - leftOld.values leftFirst) -
      (rightOld.values rightLast - rightOld.values rightFirst)) ≤ paid.charge :=
  collected.source_increment_le.trans_eq paid.charge_eq.symm

/-- Actual whole-payment success pays the original old-domain increment discrepancy at the requested tolerance. -/
theorem accurate (sufficient : paid.charge < request.tolerance) : Norm.Basic.normSq
    ((leftOld.values leftLast - leftOld.values leftFirst) -
      (rightOld.values rightLast - rightOld.values rightFirst)) < request.tolerance :=
  paid.source_increment_le.trans_lt sufficient

end Payment

end Bank

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives.Junction.Subdivision

end
